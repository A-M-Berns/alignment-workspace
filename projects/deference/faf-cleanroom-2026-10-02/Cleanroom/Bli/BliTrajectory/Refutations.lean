import Cleanroom.Bli.BliTrajectory.Lemmas

/-!
# `bli-trajectory` · Refutations: what constraints 1–4 do not imply (M7, T5), the full-scope
faith predicate (M9, Known issue 1), and `TB` on Tier B (Known issue 2)

Every refutation row here: source quoted (in the docstring), reading fixed, surviving neighbour
named.

* **The recipe history** (`recipeHistory`): a hand-built `History` over an abstract state system
  with large codes — small sentences by a base `Q`, a future state atom by a mass, `φ ⋏ σ` by a
  conditional times the mass, `φ ⋏ (σ ⋏ σ')` by the later conditional, everything else `0`. It
  satisfies **full-scope** `E1x`, `E2x`, `E3`, `E4`, `E5` under hypotheses on its parameters
  (`recipe_isBLI_Roman`), so the abstract bundle is consistent on the full scope — what fails on
  the full scope is its combination with a *Markov* prior (M9), not the bundle itself.
* **M7 (i)** `constraints_not_imply_update`: two recipe histories over one three-state system and
  one base, both `IsBLI_Roman`, agreeing on day `n₀`, differing at `stateAtom (n₀+2) q` on day
  `n₀+1`. Surviving neighbour: the Markov skeleton determines the value (`Update.lean`).
* **M7 (ii)** `faithMarginal_of_e2x` (`L`) and `faithMarginal_not_imp_e2x`: the two-table
  witness with conditionals `p ± δ`.
* **M9** `e2x_full_scope_fails`: for the tent instance from an interior base, `bli-found`'s
  full-scope `E2x` is false (a day-`(n+1)` candidate atom becomes small by day
  `max (n+2) (tokenSize σ')`, the day-`m` table sends it to `0`, and the chain through both
  atoms has positive mass).
* **Known issue 2** `tb_refuted`: `TB` on every sentence fails for the tent instance at a Tier-B
  sentence.
-/

namespace Cleanroom.Bli.BliTrajectory

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite

open Classical

noncomputable section

/-! ## The recipe history over an abstract system -/

/-- The future-candidate-atom test over an abstract system (no coding).
Source: mandate M7 (hand-built histories "by cases on the sentence")
Kind: D
Fidelity: n/a -/
def stateOf (S : StateSystem) (n : ℕ) : Sentence → Option (ℕ × ℕ)
  | .atom a => match stateData a with
      | some (m, q) => if n < m ∧ q ∈ S.states m then some (m, q) else none
      | none => none
  | _ => none

/-- `stateOf` on a future candidate atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateOf_stateAtom (S : StateSystem) {n m q : ℕ} (hnm : n < m) (hq : q ∈ S.states m) :
    stateOf S n (stateAtom m q) = some (m, q) := by
  rw [stateAtom_eq_atom]; simp [stateOf, hnm, hq]

/-- `stateOf` on a conjunction is `none`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma stateOf_and (S : StateSystem) (n : ℕ) (φ χ : Sentence) :
    stateOf S n (φ ⋏ χ) = none := rfl

/-- `stateOf` on a conjunction (constructor form).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma stateOf_and' (S : StateSystem) (n : ℕ) (φ χ : Sentence) :
    stateOf S n (Formula.and φ χ) = none := rfl

/-- `stateOf` on `⊥` is `none`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma stateOf_bot (S : StateSystem) (n : ℕ) : stateOf S n (⊥ : Sentence) = none := rfl

/-- Inversion of `stateOf = some`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateOf_eq_some {S : StateSystem} {n : ℕ} {ψ : Sentence} {m q : ℕ}
    (h : stateOf S n ψ = some (m, q)) : ψ = stateAtom m q ∧ n < m ∧ q ∈ S.states m := by
  cases ψ with
  | atom a =>
    simp only [stateOf] at h
    revert h
    cases hs : stateData a with
    | none => intro h; cases h
    | some x =>
      obtain ⟨m', q'⟩ := x
      intro h
      dsimp only at h
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨atom_eq_stateAtom_of_stateData hs, hc⟩
  | falsum => cases h
  | and _ _ => cases h
  | or _ _ => cases h
  | imp _ _ => cases h

/-- **The recipe on large sentences** (day `n` fixed): a future candidate atom → its mass;
`φ ⋏ σ` → `cond σ φ · mass σ` (`0` if `φ` is a same-day different atom — exclusivity);
`φ ⋏ (σ ⋏ σ')` → `cond σ' φ · (cond σ' σ · mass σ')` (the later state prices); else `0`. The
"else `0`" prices every other large shape — two-step chains `σ_{n+2} ⋏ σ_{n+1}`, disjunctions —
at `0`: the bundle `E1x`–`E5` never reads those sentences, which is why the full-scope bundle is
easy to satisfy and why `constraints_not_imply_update_direct` is easy (the bundle is silent on
`σ_{n+2} ⋏ σ_{n+1}`; audit r2 adversarial N8).
Source: mandate M7 (hand-built histories)
Kind: D
Fidelity: n/a -/
def recipeLarge (S : StateSystem) (mass : ℕ → ℕ → ℝ) (cond : ℕ → ℕ → Sentence → ℝ) (n : ℕ) :
    Sentence → ℝ
  | .atom a => match stateOf S n (.atom a) with
      | some (m, q) => mass m q
      | none => 0
  | .and φ χ => match stateOf S n χ with
      | some (m, q) =>
          match stateOf S n φ with
          | some (m', q') => if m' = m ∧ q' ≠ q then 0 else cond m q φ * mass m q
          | none => cond m q φ * mass m q
      | none =>
          match χ with
          | .and σ₁ σ₂ =>
              match stateOf S n σ₁, stateOf S n σ₂ with
              | some (m, q₁), some (o, q₂) =>
                  if m < o then cond o q₂ φ * (cond o q₂ σ₁ * mass o q₂) else 0
              | _, _ => 0
          | _ => 0
  | _ => 0

/-- **The recipe history**: small sentences by the base, large ones by `recipeLarge`.
Source: mandate M7 (hand-built histories)
Kind: D
Fidelity: n/a -/
def recipeHistory (Q : History) (S : StateSystem) (mass : ℕ → ℕ → ℕ → ℝ)
    (cond : ℕ → ℕ → ℕ → Sentence → ℝ) : History :=
  fun n ψ => if SmallOn n ψ then Q n ψ else recipeLarge S (mass n) (cond n) n ψ

variable {S : StateSystem} {mass : ℕ → ℕ → ℝ} {cond : ℕ → ℕ → Sentence → ℝ} {n : ℕ}

/-- The recipe on a future candidate atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma recipeLarge_stateAtom {m q : ℕ} (hnm : n < m) (hq : q ∈ S.states m) :
    recipeLarge S mass cond n (stateAtom m q) = mass m q := by
  rw [stateAtom_eq_atom]
  simp [recipeLarge, stateOf, hnm, hq]

/-- The recipe on `φ ⋏ σ` when `φ` is not a same-day atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma recipeLarge_and_stateAtom {m q : ℕ} (hnm : n < m) (hq : q ∈ S.states m) {φ : Sentence}
    (hφ : ∀ q', φ ≠ stateAtom m q') :
    recipeLarge S mass cond n (φ ⋏ stateAtom m q) = cond m q φ * mass m q := by
  change recipeLarge S mass cond n (.and φ (stateAtom m q)) = _
  simp only [recipeLarge, stateOf_stateAtom S hnm hq]
  cases hs : stateOf S n φ with
  | none => rfl
  | some x =>
    obtain ⟨m', q'⟩ := x
    obtain ⟨rfl, -, -⟩ := stateOf_eq_some hs
    have : m' ≠ m := fun h => hφ q' (by rw [h])
    simp [this]

/-- The recipe on a same-day pair with different codes is `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma recipeLarge_same_day {m q₁ q₂ : ℕ} (hnm : n < m) (hq₁ : q₁ ∈ S.states m)
    (hq₂ : q₂ ∈ S.states m) (hne : q₁ ≠ q₂) :
    recipeLarge S mass cond n (stateAtom m q₁ ⋏ stateAtom m q₂) = 0 := by
  change recipeLarge S mass cond n (.and (stateAtom m q₁) (stateAtom m q₂)) = _
  simp [recipeLarge, stateOf_stateAtom S hnm hq₁, stateOf_stateAtom S hnm hq₂, hne]

/-- The recipe on a two-atom chain of increasing days.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma recipeLarge_two {m o q₁ q₂ : ℕ} (hnm : n < m) (hq₁ : q₁ ∈ S.states m) (hno : n < o)
    (hq₂ : q₂ ∈ S.states o) (hmo : m < o) :
    recipeLarge S mass cond n (stateAtom m q₁ ⋏ stateAtom o q₂) =
      cond o q₂ (stateAtom m q₁) * mass o q₂ := by
  change recipeLarge S mass cond n (.and (stateAtom m q₁) (stateAtom o q₂)) = _
  simp [recipeLarge, stateOf_stateAtom S hnm hq₁, stateOf_stateAtom S hno hq₂, hmo.ne]

/-- The recipe on `φ ⋏ (σ ⋏ σ')`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma recipeLarge_and_two {m o q₁ q₂ : ℕ} (hnm : n < m) (hq₁ : q₁ ∈ S.states m) (hno : n < o)
    (hq₂ : q₂ ∈ S.states o) (hmo : m < o) (φ : Sentence) :
    recipeLarge S mass cond n (φ ⋏ (stateAtom m q₁ ⋏ stateAtom o q₂)) =
      cond o q₂ φ * (cond o q₂ (stateAtom m q₁) * mass o q₂) := by
  change recipeLarge S mass cond n (.and φ (.and (stateAtom m q₁) (stateAtom o q₂))) = _
  simp [recipeLarge, stateOf_stateAtom S hnm hq₁, stateOf_stateAtom S hno hq₂, hmo]

/-- The scope of faith grows with the day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Sminus_mono_self {m o : ℕ} (h : m ≤ o) : Sminus m m ⊆ Sminus o o := by
  intro φ hφ
  rw [mem_Sminus] at hφ ⊢
  exact ⟨hφ.1.mono h, fun a ha => lt_of_lt_of_le (hφ.2 a ha) h⟩

/-! ### The recipe satisfies the full-scope bundle -/

variable {Q : History} {massF : ℕ → ℕ → ℕ → ℝ} {condF : ℕ → ℕ → ℕ → Sentence → ℝ}

/-- Largeness of the candidates of an abstract system (the hypothesis every recipe row carries).
Source: mandate M7
Kind: D
Fidelity: n/a -/
def LargeStates (S : StateSystem) : Prop := ∀ m, ∀ q ∈ S.states m, ∀ n ≤ m, ¬ SmallOn n (stateAtom m q)

/-- `recipe_E1x`.
Source: mandate M7
Kind: L
Fidelity: exact -/
lemma recipe_E1x : E1x Q (recipeHistory Q S massF condF) := by
  intro n φ hφ
  unfold recipeHistory
  rw [if_pos (mem_smallSet.mp hφ)]

/-- `recipe_E2x` (full scope): when the conditional agrees with the tables on the scope.
Source: mandate M7
Kind: L
Fidelity: exact (full scope) -/
lemma recipe_E2x (hl : LargeStates S)
    (hcond : ∀ n m q φ, n < m → q ∈ S.states m → φ ∈ Sminus m m → condF n m q φ = S.val m q φ) :
    E2x S (recipeHistory Q S massF condF) := by
  intro n m hnm q hq φ hφ
  have hσ : ¬ SmallOn n (stateAtom m q) := hl m q hq n hnm.le
  unfold recipeHistory
  rw [if_neg (not_smallOn_and_of_right hσ), if_neg hσ, recipeLarge_stateAtom hnm hq,
    recipeLarge_and_stateAtom hnm hq (fun q' h => by
      rw [h] at hφ; exact stateAtom_notMem_Sminus m m q' hφ), hcond n m q φ hnm hq hφ]

/-- `recipe_E3` (full scope).
Source: mandate M7
Kind: L
Fidelity: exact (full scope) -/
lemma recipe_E3 (hl : LargeStates S)
    (hcond : ∀ n m q φ, n < m → q ∈ S.states m → φ ∈ Sminus m m → condF n m q φ = S.val m q φ) :
    E3 S (recipeHistory Q S massF condF) := by
  intro n m o hnm hmo q₁ hq₁ q₂ hq₂ φ hφ
  have hno : n < o := hnm.trans hmo
  have hσ : ¬ SmallOn n (stateAtom m q₁ ⋏ stateAtom o q₂) :=
    not_smallOn_and_of_left (hl m q₁ hq₁ n hnm.le)
  unfold recipeHistory
  rw [if_neg (not_smallOn_and_of_right hσ), if_neg hσ, recipeLarge_two hnm hq₁ hno hq₂ hmo,
    recipeLarge_and_two hnm hq₁ hno hq₂ hmo, hcond n o q₂ φ hno hq₂ (Sminus_mono_self hmo.le hφ)]

/-- `recipe_E4`: when the base is the mass-weighted table average on every small sentence.
Source: mandate M7
Kind: L
Fidelity: exact -/
lemma recipe_E4 (hl : LargeStates S)
    (h4 : ∀ n, ∀ φ ∈ smallSet n,
      Q n φ = ∑ q ∈ S.states (n + 1), massF n (n + 1) q * S.val (n + 1) q φ) :
    E4 S (recipeHistory Q S massF condF) := by
  intro n φ hφ
  unfold recipeHistory
  rw [if_pos (mem_smallSet.mp hφ), h4 n φ hφ]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [if_neg (hl (n + 1) q hq n (Nat.le_succ n)), recipeLarge_stateAtom (Nat.lt_succ_self n) hq]

/-- `recipe_E5`: when the masses sum to one.
Source: mandate M7
Kind: L
Fidelity: exact -/
lemma recipe_E5 (hl : LargeStates S) (h5 : ∀ n, ∑ q ∈ S.states (n + 1), massF n (n + 1) q = 1) :
    E5 S (recipeHistory Q S massF condF) := by
  intro n
  constructor
  · rw [← h5 n]
    refine Finset.sum_congr rfl fun q hq => ?_
    unfold recipeHistory
    rw [if_neg (hl (n + 1) q hq n (Nat.le_succ n)), recipeLarge_stateAtom (Nat.lt_succ_self n) hq]
  · intro q₁ hq₁ q₂ hq₂ hne
    unfold recipeHistory
    rw [if_neg (not_smallOn_and_of_left (hl (n + 1) q₁ hq₁ n (Nat.le_succ n))),
      recipeLarge_same_day (Nat.lt_succ_self n) hq₁ hq₂ hne]

/-- **The full-scope Roman bundle is consistent**: the recipe with the tables as conditionals
satisfies `IsBLI_Roman S Q P` on the **full** scope, given large candidates, masses summing
to one, and a base equal to the mass-weighted table average. (What is inconsistent with the
full scope is a Markov prior — M9 — not the bundle.)
Source: mandate M7; Known issue 1 (contrast)
Kind: C
Fidelity: exact (full scope)
Hyps: (a) `LargeStates S`, `h4`, `h5` (explicit; the witnesses below discharge them) -/
theorem recipe_isBLI_Roman (hl : LargeStates S)
    (h4 : ∀ n, ∀ φ ∈ smallSet n,
      Q n φ = ∑ q ∈ S.states (n + 1), massF n (n + 1) q * S.val (n + 1) q φ)
    (h5 : ∀ n, ∑ q ∈ S.states (n + 1), massF n (n + 1) q = 1) :
    IsBLI_Roman S Q (recipeHistory Q S massF (fun _ m q φ => S.val m q φ)) :=
  ⟨recipe_E1x, recipe_E2x hl (fun _ _ _ _ _ _ _ => rfl), recipe_E3 hl (fun _ _ _ _ _ _ _ => rfl),
    recipe_E4 hl h4, recipe_E5 hl h5⟩

/-! ## M7 (i): constraints 1–4 do not determine the update on large sentences -/

/-- Three large codes per day: `4^{sizeBound m}`, `+1`, `+2`.
Source: mandate M7 (i)
Kind: D
Fidelity: n/a -/
def threeCodes (m : ℕ) : Finset ℕ := {4 ^ sizeBound m, 4 ^ sizeBound m + 1, 4 ^ sizeBound m + 2}

/-- The three-state system: table `i ↦ i/2` for the code `4^{sizeBound m} + i` (constant in the
sentence), so the tables are non-constant across states.
Source: mandate M7 (i)
Kind: D
Fidelity: n/a -/
def threeSystem : StateSystem where
  states := threeCodes
  val m q _ := ((q - 4 ^ sizeBound m : ℕ) : ℝ) / 2
  actual m := 4 ^ sizeBound m
  actual_mem _ := by simp [threeCodes]

/-- A code `≥ 4^{sizeBound m}` is large.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sizeBound_le_log_of_le {m q : ℕ} (h : 4 ^ sizeBound m ≤ q) : sizeBound m ≤ Nat.log 4 q :=
  calc sizeBound m = Nat.log 4 (4 ^ sizeBound m) := (Nat.log_pow (by norm_num) _).symm
    _ ≤ Nat.log 4 q := Nat.log_mono_right h

/-- The three-state system has large candidates.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma threeSystem_large : LargeStates threeSystem := by
  intro m q hq
  apply stateAtom_large
  apply sizeBound_le_log_of_le
  simp only [threeSystem, threeCodes, Finset.mem_insert, Finset.mem_singleton] at hq
  omega

/-- The mass vector `(¼, ½, ¼)` on the three codes of day `m`.
Source: mandate M7 (i)
Kind: D
Fidelity: n/a -/
def massA (m q : ℕ) : ℝ :=
  if q = 4 ^ sizeBound m then 1 / 4 else if q = 4 ^ sizeBound m + 1 then 1 / 2 else 1 / 4

/-- The mass vector `(⅓, ⅓, ⅓)`.
Source: mandate M7 (i)
Kind: D
Fidelity: n/a -/
def massB (_ _ : ℕ) : ℝ := 1 / 3

/-- Both mass vectors give the same table average `½` and sum to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massA_sums (m : ℕ) :
    ∑ q ∈ threeCodes m, massA m q * ((q - 4 ^ sizeBound m : ℕ) : ℝ) / 2 = 1 / 2 ∧
      ∑ q ∈ threeCodes m, massA m q = 1 := by
  have h1 : 4 ^ sizeBound m ≠ 4 ^ sizeBound m + 1 := by omega
  have h2 : 4 ^ sizeBound m ≠ 4 ^ sizeBound m + 2 := by omega
  have h3 : 4 ^ sizeBound m + 1 ≠ 4 ^ sizeBound m + 2 := by omega
  simp only [threeCodes, massA]
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_singleton, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_singleton]
  simp [h1, h2, h3]
  norm_num

/-- `massB_sums`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massB_sums (m : ℕ) :
    ∑ q ∈ threeCodes m, massB m q * ((q - 4 ^ sizeBound m : ℕ) : ℝ) / 2 = 1 / 2 ∧
      ∑ q ∈ threeCodes m, massB m q = 1 := by
  have h1 : 4 ^ sizeBound m ≠ 4 ^ sizeBound m + 1 := by omega
  have h2 : 4 ^ sizeBound m ≠ 4 ^ sizeBound m + 2 := by omega
  have h3 : 4 ^ sizeBound m + 1 ≠ 4 ^ sizeBound m + 2 := by omega
  simp only [threeCodes, massB]
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_singleton, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_singleton]
  simp
  norm_num

/-- The two mass schedules of M7 (i): `massA` every day, vs `massB` on day `n₀+1` only.
Source: mandate M7 (i)
Kind: D
Fidelity: n/a -/
def massSched₁ (_ : ℕ) : ℕ → ℕ → ℕ → ℝ := fun _ m q => massA m q

/-- `massSched₂`.
Source: mandate M7 (i)
Kind: D
Fidelity: n/a -/
def massSched₂ (n₀ : ℕ) : ℕ → ℕ → ℕ → ℝ := fun n m q => if n = n₀ + 1 then massB m q else massA m q

/-- The constant-`½` base.
Source: mandate M7 (i)
Kind: D
Fidelity: n/a -/
def halfHistory : History := fun _ _ => 1 / 2

/-- **`constraints_not_imply_update` — constraints 1–4 (with the partition) do not determine
the update on large sentences** (bli-soto-a-005; `main.tex:440` "we can see `𝐏`'s updates … as a
Bayesian update"). Reading: the update identity on a day-`(n₀+2)` state atom at day `n₀+1` is
not a consequence of `IsBLI_Roman` plus agreement on day `n₀`. Witness: `threeSystem` (tables
`0, ½, 1`, non-constant), base `½`, two recipe histories with day-`(n₀+1)` masses `(¼, ½, ¼)` vs
`(⅓, ⅓, ⅓)` — both `IsBLI_Roman` on the full scope, equal on day `n₀`, different at
`stateAtom (n₀+2) (4^{sizeBound}+1)` on day `n₀+1` (`½` vs `⅓`). Surviving neighbour: the Markov
skeleton determines the value (`Update.bli_update_tierA_exact`). N+ on the coordinate that
matters (two different superbeliefs with non-constant tables); the other days are a constant
scaffold (disclosed).
Source: bli-soto-a-005; Appendix B (`main.tex:440`); mandate M7 (i)
Kind: P
Fidelity: exact (refutation of the implication)
Hyps: (a) none -/
theorem constraints_not_imply_update (n₀ : ℕ) :
    ∃ (S : StateSystem) (Q P₁ P₂ : History), IsBLI_Roman S Q P₁ ∧ IsBLI_Roman S Q P₂ ∧
      (∀ ψ, P₁ n₀ ψ = P₂ n₀ ψ) ∧
      ∃ q ∈ S.states (n₀ + 2),
        P₁ (n₀ + 1) (stateAtom (n₀ + 2) q) ≠ P₂ (n₀ + 1) (stateAtom (n₀ + 2) q) := by
  refine ⟨threeSystem, halfHistory,
    recipeHistory halfHistory threeSystem (massSched₁ n₀) (fun _ m q φ => threeSystem.val m q φ),
    recipeHistory halfHistory threeSystem (massSched₂ n₀) (fun _ m q φ => threeSystem.val m q φ),
    ?_, ?_, ?_, ?_⟩
  · refine recipe_isBLI_Roman threeSystem_large (fun n φ _ => ?_) (fun n => (massA_sums _).2)
    show (1 / 2 : ℝ) = ∑ q ∈ threeCodes (n + 1), massA (n + 1) q * (((q - 4 ^ sizeBound (n + 1) : ℕ) : ℝ) / 2)
    rw [← (massA_sums (n + 1)).1]
    exact Finset.sum_congr rfl fun q _ => by ring
  · refine recipe_isBLI_Roman threeSystem_large (fun n φ _ => ?_) (fun n => ?_)
    · show (1 / 2 : ℝ) = ∑ q ∈ threeCodes (n + 1),
        (if n = n₀ + 1 then massB (n + 1) q else massA (n + 1) q) *
          (((q - 4 ^ sizeBound (n + 1) : ℕ) : ℝ) / 2)
      by_cases h : n = n₀ + 1
      · simp only [h, if_true]
        rw [← (massB_sums (n₀ + 1 + 1)).1]
        exact Finset.sum_congr rfl fun q _ => by ring
      · simp only [h, if_false]
        rw [← (massA_sums (n + 1)).1]
        exact Finset.sum_congr rfl fun q _ => by ring
    · show ∑ q ∈ threeCodes (n + 1), (if n = n₀ + 1 then massB (n + 1) q else massA (n + 1) q) = 1
      by_cases h : n = n₀ + 1
      · simp only [h, if_true]; exact (massB_sums _).2
      · simp only [h, if_false]; exact (massA_sums _).2
  · intro ψ
    unfold recipeHistory
    have : massSched₂ n₀ n₀ = massSched₁ n₀ n₀ := by
      funext m q; simp [massSched₁, massSched₂]
    rw [this]
  · refine ⟨4 ^ sizeBound (n₀ + 2) + 1, by simp [threeSystem, threeCodes], ?_⟩
    have hq : 4 ^ sizeBound (n₀ + 2) + 1 ∈ threeSystem.states (n₀ + 2) := by
      simp [threeSystem, threeCodes]
    have hl : ¬ SmallOn (n₀ + 1) (stateAtom (n₀ + 2) (4 ^ sizeBound (n₀ + 2) + 1)) :=
      threeSystem_large (n₀ + 2) _ hq (n₀ + 1) (Nat.le_succ _)
    unfold recipeHistory
    rw [if_neg hl, if_neg hl, recipeLarge_stateAtom (Nat.lt_succ_self _) hq,
      recipeLarge_stateAtom (Nat.lt_succ_self _) hq]
    simp only [massSched₁, massSched₂, if_true, massA, massB]
    norm_num

/-- **`constraints_not_imply_update_direct` — the direct form of M7 (i)**: the first history of
`constraints_not_imply_update` (masses `(¼, ½, ¼)` every day) is `IsBLI_Roman` on the full
scope and violates the product-form update `𝐏_{n₀+1}(ψ) · 𝐏_{n₀}(σ) = 𝐏_{n₀}(ψ ⋏ σ)` at
`ψ = σ_{n₀+2, 4^s+1}`, `σ` the realized day-`(n₀+1)` atom, at **positive conditioning mass**:
`𝐏_{n₀}(σ) = ¼`, `𝐏_{n₀+1}(ψ) = ½`, `𝐏_{n₀}(ψ ⋏ σ) = 0` — so `TB` fails there outright. The
two-history form leaves the reader to check positivity; this one is self-contained (audit r1
adversarial N3, probe `RefutationDirect.P₁_violates_update`). Same incoherent scaffold as the
two-history form (disclosed there).
Source: bli-soto-a-005; Appendix B (`main.tex:440`); mandate M7 (i)
Kind: P
Fidelity: exact (refutation, direct form)
Hyps: (a) none -/
theorem constraints_not_imply_update_direct (n₀ : ℕ) :
    ∃ (S : StateSystem) (Q P : History), IsBLI_Roman S Q P ∧
      P n₀ (stateAtom (n₀ + 1) (S.actual (n₀ + 1))) = 1 / 4 ∧
      ∃ q ∈ S.states (n₀ + 2),
        P (n₀ + 1) (stateAtom (n₀ + 2) q) = 1 / 2 ∧
        P n₀ (stateAtom (n₀ + 2) q ⋏ stateAtom (n₀ + 1) (S.actual (n₀ + 1))) = 0 := by
  have ha : 4 ^ sizeBound (n₀ + 1) ∈ threeSystem.states (n₀ + 1) := by
    simp [threeSystem, threeCodes]
  have hq : 4 ^ sizeBound (n₀ + 2) + 1 ∈ threeSystem.states (n₀ + 2) := by
    simp [threeSystem, threeCodes]
  have hlσ : ¬ SmallOn n₀ (stateAtom (n₀ + 1) (4 ^ sizeBound (n₀ + 1))) :=
    threeSystem_large (n₀ + 1) _ ha n₀ (Nat.le_succ _)
  have hlψ : ¬ SmallOn (n₀ + 1) (stateAtom (n₀ + 2) (4 ^ sizeBound (n₀ + 2) + 1)) :=
    threeSystem_large (n₀ + 2) _ hq (n₀ + 1) (Nat.le_succ _)
  have hψσ : ∀ q', stateAtom (n₀ + 2) (4 ^ sizeBound (n₀ + 2) + 1) ≠ stateAtom (n₀ + 1) q' := by
    intro q' h
    have := (stateAtom_inj.mp h).1
    omega
  have h1 : 4 ^ sizeBound (n₀ + 2) + 1 ≠ 4 ^ sizeBound (n₀ + 2) := by omega
  refine ⟨threeSystem, halfHistory,
    recipeHistory halfHistory threeSystem (massSched₁ n₀) (fun _ m q φ => threeSystem.val m q φ),
    ?_, ?_, 4 ^ sizeBound (n₀ + 2) + 1, hq, ?_, ?_⟩
  · refine recipe_isBLI_Roman threeSystem_large (fun n φ _ => ?_) (fun n => (massA_sums _).2)
    show (1 / 2 : ℝ) = ∑ q ∈ threeCodes (n + 1),
      massA (n + 1) q * (((q - 4 ^ sizeBound (n + 1) : ℕ) : ℝ) / 2)
    rw [← (massA_sums (n + 1)).1]
    exact Finset.sum_congr rfl fun q _ => by ring
  · show recipeHistory halfHistory threeSystem (massSched₁ n₀) (fun _ m q φ => threeSystem.val m q φ)
      n₀ (stateAtom (n₀ + 1) (4 ^ sizeBound (n₀ + 1))) = 1 / 4
    unfold recipeHistory
    rw [if_neg hlσ, recipeLarge_stateAtom (Nat.lt_succ_self _) ha]
    simp [massSched₁, massA]
  · unfold recipeHistory
    rw [if_neg hlψ, recipeLarge_stateAtom (Nat.lt_succ_self _) hq]
    simp [massSched₁, massA, h1]
  · show recipeHistory halfHistory threeSystem (massSched₁ n₀) (fun _ m q φ => threeSystem.val m q φ)
      n₀ (stateAtom (n₀ + 2) (4 ^ sizeBound (n₀ + 2) + 1) ⋏
        stateAtom (n₀ + 1) (4 ^ sizeBound (n₀ + 1))) = 0
    unfold recipeHistory
    rw [if_neg (not_smallOn_and_of_right hlσ),
      recipeLarge_and_stateAtom (Nat.lt_succ_self _) ha hψσ]
    simp [threeSystem]

/-! ## M7 (ii): faith in the marginal -/

/-- **`E2x` implies `FaithMarginal`** (bli-slides-015 (a)): sum constraint 2 over the states whose
table prices `φ` at `x`. A `Finset.sum_congr`.
Source: bli-slides-015 (a)/(b); mandate M7 (ii)
Kind: L
Fidelity: exact -/
theorem faithMarginal_of_e2x {S : StateSystem} {P : History} (h : E2x S P) : FaithMarginal S P := by
  intro n m hnm φ hφ x
  unfold marginalJoint marginalMass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.mem_filter] at hq
  rw [h n m hnm q hq.1 φ hφ, hq.2]

/-- Two large codes per day.
Source: mandate M7 (ii)
Kind: D
Fidelity: n/a -/
def twoCodes (m : ℕ) : Finset ℕ := {4 ^ sizeBound m, 4 ^ sizeBound m + 1}

/-- The two-state system with identical constant tables `p` — two codes, one table (audit r2
adversarial N3; B1's own system is injective on candidates, and the distinct-table refutation
is `TriState.lean`).
Source: mandate M7 (ii) (bli-soto-a-009's two-table witness)
Kind: D
Fidelity: n/a -/
def twoSystem (p : ℝ) : StateSystem where
  states := twoCodes
  val _ _ _ := p
  actual m := 4 ^ sizeBound m
  actual_mem _ := by simp [twoCodes]

/-- `twoSystem_large`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoSystem_large (p : ℝ) : LargeStates (twoSystem p) := by
  intro m q hq
  apply stateAtom_large
  apply sizeBound_le_log_of_le
  simp only [twoSystem, twoCodes, Finset.mem_insert, Finset.mem_singleton] at hq
  omega

/-- The conditionals `p + δ` (first code) and `p − δ` (second code).
Source: mandate M7 (ii)
Kind: D
Fidelity: n/a -/
def skewCond (p δ : ℝ) : ℕ → ℕ → ℕ → Sentence → ℝ :=
  fun _ m q _ => if q = 4 ^ sizeBound m then p + δ else p - δ

/-- **`faithMarginal_not_imp_e2x` — faith in the marginal does not imply faith in the state**
(bli-slides-015 (b), bli-soto-a-009). Witness: `twoSystem p` (both tables price everything at
`p`), base `p`, masses `½, ½`, conditionals `p + δ` and `p − δ` with `0 < p − δ`, `p + δ < 1`,
`δ ≠ 0`. `E1x`, `E4`, `E5` and `FaithMarginal` hold (the two conditionals average to `p`), and
`E2x` fails at `(0, 1, 4^{sizeBound 1}, ⊥)`: `(p+δ)/2 ≠ p/2`. N+ on the coordinate that
matters: two distinct positive-mass states with different interior conditionals; the tables are
identical (that is the point of the witness) and the other days are a constant scaffold
(disclosed). Surviving neighbour: refinement-invariant trust, which *is* `E2x`.
Source: bli-slides-015 (b); bli-soto-a-009; mandate M7 (ii)
Kind: P
Fidelity: exact (refutation of the converse)
Hyps: (a) `0 < p − δ`, `p + δ < 1`, `δ ≠ 0` (the witness's parameters) -/
theorem faithMarginal_not_imp_e2x (p δ : ℝ) (h0 : 0 < p - δ) (h1 : p + δ < 1) (hδ : δ ≠ 0) :
    ∃ (S : StateSystem) (Q P : History), E1x Q P ∧ E4 S P ∧ E5 S P ∧ FaithMarginal S P ∧ ¬ E2x S P := by
  have hl := twoSystem_large p
  have hne : ∀ m, 4 ^ sizeBound m ≠ 4 ^ sizeBound m + 1 := fun m => by omega
  refine ⟨twoSystem p, fun _ _ => p,
    recipeHistory (fun _ _ => p) (twoSystem p) (fun _ _ _ => 1 / 2) (skewCond p δ),
    recipe_E1x, recipe_E4 hl ?_, recipe_E5 hl ?_, ?_, ?_⟩
  · intro n φ _
    show p = ∑ q ∈ twoCodes (n + 1), (1 / 2 : ℝ) * p
    simp only [twoCodes]
    rw [Finset.sum_insert (by simp), Finset.sum_singleton]; ring
  · intro n
    show ∑ q ∈ twoCodes (n + 1), (1 / 2 : ℝ) = 1
    simp only [twoCodes]
    rw [Finset.sum_insert (by simp), Finset.sum_singleton]; norm_num
  · intro n m hnm φ hφ x
    unfold marginalJoint marginalMass
    by_cases hx : x = p
    · rw [hx]
      have hfilt : (twoCodes m).filter (fun q => (twoSystem p).val m q φ = p) = twoCodes m := by
        apply Finset.filter_true_of_mem; intro q _; rfl
      show ∑ q ∈ (twoCodes m).filter (fun q => (twoSystem p).val m q φ = p),
          recipeHistory (fun _ _ => p) (twoSystem p) (fun _ _ _ => 1 / 2) (skewCond p δ) n
            (φ ⋏ stateAtom m q) =
        p * ∑ q ∈ (twoCodes m).filter (fun q => (twoSystem p).val m q φ = p),
          recipeHistory (fun _ _ => p) (twoSystem p) (fun _ _ _ => 1 / 2) (skewCond p δ) n
            (stateAtom m q)
      rw [hfilt]
      have hq₁ : 4 ^ sizeBound m ∈ (twoSystem p).states m := by simp [twoSystem, twoCodes]
      have hq₂ : 4 ^ sizeBound m + 1 ∈ (twoSystem p).states m := by simp [twoSystem, twoCodes]
      have hφ' : ∀ q', φ ≠ stateAtom m q' := fun q' h => by
        rw [h] at hφ; exact stateAtom_notMem_Sminus m m q' hφ
      simp only [twoCodes]
      rw [Finset.sum_insert (by simp), Finset.sum_singleton,
        Finset.sum_insert (by simp), Finset.sum_singleton]
      unfold recipeHistory
      rw [if_neg (not_smallOn_and_of_right (hl m _ hq₁ n hnm.le)),
        if_neg (not_smallOn_and_of_right (hl m _ hq₂ n hnm.le)),
        if_neg (hl m _ hq₁ n hnm.le), if_neg (hl m _ hq₂ n hnm.le),
        recipeLarge_and_stateAtom hnm hq₁ hφ', recipeLarge_and_stateAtom hnm hq₂ hφ',
        recipeLarge_stateAtom hnm hq₁, recipeLarge_stateAtom hnm hq₂]
      simp only [skewCond, if_true]
      split_ifs with hh
      · omega
      · ring
    · have hfilt : (twoCodes m).filter (fun q => (twoSystem p).val m q φ = x) = ∅ := by
        apply Finset.filter_false_of_mem; intro q _; exact fun h => hx h.symm
      show ∑ q ∈ (twoCodes m).filter (fun q => (twoSystem p).val m q φ = x), _ =
        x * ∑ q ∈ (twoCodes m).filter (fun q => (twoSystem p).val m q φ = x), _
      rw [hfilt]; simp
  · intro hE2
    have hq₁ : 4 ^ sizeBound 1 ∈ (twoSystem p).states 1 := by simp [twoSystem, twoCodes]
    have := hE2 0 1 (by norm_num) _ hq₁ ⊥ (falsum_mem_Sminus 1 1)
    unfold recipeHistory at this
    rw [if_neg (not_smallOn_and_of_right (hl 1 _ hq₁ 0 (by norm_num))),
      if_neg (hl 1 _ hq₁ 0 (by norm_num)), recipeLarge_and_stateAtom (by norm_num) hq₁
        (fun q' h => by cases h), recipeLarge_stateAtom (by norm_num) hq₁] at this
    simp only [skewCond, if_true, twoSystem] at this
    apply hδ
    linarith

/-! ## M9 — Known issue 1 as a theorem: the full-scope faith predicate fails for the tent instance -/

/-- The mesh is monotone (`d m ∣ d (m+1)`, `0 < d`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mesh_d_mono (𝓜 : Mesh) {i j : ℕ} (h : i ≤ j) : 𝓜.d i ≤ 𝓜.d j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (Nat.le_of_dvd (𝓜.d_pos _) (𝓜.d_dvd _))

/-- The uniform table `1 / d_j` on day `j` (interior when `2 ≤ d_j`).
Source: mandate M9
Kind: D
Fidelity: n/a -/
def uniformTable (𝓜 : Mesh) (j : ℕ) : Table smallIndex j := fun _ => 1 / (𝓜.d j : ℚ)

/-- `uniformTable_mem_grid`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma uniformTable_mem_grid (𝓜 : Mesh) (j : ℕ) : uniformTable 𝓜 j ∈ grid smallIndex 𝓜.d j := by
  rw [mem_grid_iff]; intro φ
  exact mem_gridVals_iff.mpr ⟨1, 𝓜.d_pos j, by simp [uniformTable]⟩

/-- `uniformTable_interior`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma uniformTable_interior (𝓜 : Mesh) {j : ℕ} (hd : 2 ≤ 𝓜.d j) :
    ∀ φ, 0 < uniformTable 𝓜 j φ ∧ uniformTable 𝓜 j φ < 1 := by
  intro φ
  have h : (2 : ℚ) ≤ 𝓜.d j := by exact_mod_cast hd
  simp only [uniformTable]
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]; linarith

/-- The tent law from an interior table charges every grid table (its face is the whole grid).
Source: `bli-finite` `tentLaw_pos_iff`
Kind: L
Fidelity: n/a -/
lemma tentLaw_pos_of_interior {𝓜 : Mesh} {j : ℕ} {t : Table smallIndex j}
    (ht : ∀ φ, 0 < t φ ∧ t φ < 1) {A : Table smallIndex (j + 1)}
    (hA : A ∈ grid smallIndex 𝓜.d (j + 1)) : 0 < tentLaw 𝓜 j t A := by
  have htu : t.InUnit := fun φ => ⟨(ht φ).1.le, (ht φ).2.le⟩
  rw [tentLaw_pos_iff htu, mem_faceProd_iff]
  refine ⟨hA, fun φ hφ => ?_⟩
  rcases hφ with h | h
  · exact absurd h (ht φ).1.ne'
  · exact absurd h (ht φ).2.ne

/-- **The face table** of a day-`n` table `t` on a day `j`: copies `t`'s `0/1` coordinates and
puts `1/d_j` on every other coordinate (interior day-`n` coordinates and new ones). It lies in
the product face of `t` at the step `n → n+1` and in the product face of the previous day's
face table at every later step (`d_j ≥ 2`), so the tent charges the whole path from *any*
unit-cube start — no interior base needed (repair round 1: audit r1 fidelity N3 / adversarial
N2, whose `hint` excluded every propositionally coherent base).
Source: mandate M9; `bli-finite` `faceProd`
Kind: D
Fidelity: n/a -/
def faceTable (𝓜 : Mesh) {n : ℕ} (t : Table smallIndex n) (j : ℕ) : Table smallIndex j :=
  fun ψ => if h : ψ.1 ∈ smallSet n then
      (if t ⟨ψ.1, h⟩ = 0 then 0 else if t ⟨ψ.1, h⟩ = 1 then 1 else 1 / (𝓜.d j : ℚ))
    else 1 / (𝓜.d j : ℚ)

section FaceTable

variable (𝓜 : Mesh) {n : ℕ} (t : Table smallIndex n) (j : ℕ)

/-- `1/d_j` is a grid value in `[0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma inv_d_mem (hd : 0 < 𝓜.d j) :
    (1 : ℚ) / 𝓜.d j ∈ gridVals (𝓜.d j) ∧ 0 ≤ (1 : ℚ) / 𝓜.d j ∧ (1 : ℚ) / 𝓜.d j ≤ 1 := by
  have h1 : (1 : ℚ) ≤ 𝓜.d j := by exact_mod_cast hd
  refine ⟨mem_gridVals_iff.mpr ⟨1, hd, by simp⟩, by positivity, ?_⟩
  rw [div_le_one (by linarith)]; exact h1

/-- `faceTable` on a day-`n` coordinate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma faceTable_of_mem {ψ : ↥(smallSet j)} (hψ : ψ.1 ∈ smallSet n) :
    faceTable 𝓜 t j ψ =
      (if t ⟨ψ.1, hψ⟩ = 0 then 0 else if t ⟨ψ.1, hψ⟩ = 1 then 1 else 1 / (𝓜.d j : ℚ)) := by
  unfold faceTable; rw [dif_pos hψ]

/-- `faceTable` on a new coordinate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma faceTable_of_not_mem {ψ : ↥(smallSet j)} (hψ : ψ.1 ∉ smallSet n) :
    faceTable 𝓜 t j ψ = 1 / (𝓜.d j : ℚ) := by
  unfold faceTable; rw [dif_neg hψ]

/-- `faceTable` copies `t`'s `0/1` coordinates.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma faceTable_of_zero_one {ψ : ↥(smallSet j)} (hψ : ψ.1 ∈ smallSet n)
    (h : t ⟨ψ.1, hψ⟩ = 0 ∨ t ⟨ψ.1, hψ⟩ = 1) : faceTable 𝓜 t j ψ = t ⟨ψ.1, hψ⟩ := by
  rw [faceTable_of_mem 𝓜 t j hψ]
  split_ifs with h0 h1
  · exact h0.symm
  · exact h1.symm
  · exfalso
    rcases h with h | h
    · exact h0 h
    · exact h1 h

/-- `faceTable_mem_grid`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma faceTable_mem_grid : faceTable 𝓜 t j ∈ grid smallIndex 𝓜.d j := by
  rw [mem_grid_iff]; intro ψ
  have hi := (inv_d_mem 𝓜 j (𝓜.d_pos j)).1
  by_cases hψ : ψ.1 ∈ smallSet n
  · rw [faceTable_of_mem 𝓜 t j hψ]
    split_ifs
    · exact zero_mem_gridVals _
    · exact one_mem_gridVals (𝓜.d_pos _)
    · exact hi
  · rw [faceTable_of_not_mem 𝓜 t j hψ]; exact hi

/-- `faceTable_inUnit`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma faceTable_inUnit : (faceTable 𝓜 t j).InUnit := by
  intro ψ
  have hi := (inv_d_mem 𝓜 j (𝓜.d_pos j)).2
  by_cases hψ : ψ.1 ∈ smallSet n
  · rw [faceTable_of_mem 𝓜 t j hψ]
    split_ifs <;> first | exact hi | norm_num
  · rw [faceTable_of_not_mem 𝓜 t j hψ]; exact hi

/-- A `0/1` coordinate of `faceTable` (with `d_j ≥ 2`) is one of `t`'s `0/1` coordinates.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma faceTable_zero_or_one (hd : 2 ≤ 𝓜.d j) {ψ : ↥(smallSet j)}
    (h : faceTable 𝓜 t j ψ = 0 ∨ faceTable 𝓜 t j ψ = 1) :
    ∃ hψ : ψ.1 ∈ smallSet n,
      (t ⟨ψ.1, hψ⟩ = 0 ∨ t ⟨ψ.1, hψ⟩ = 1) ∧ t ⟨ψ.1, hψ⟩ = faceTable 𝓜 t j ψ := by
  have hd2 : (2 : ℚ) ≤ 𝓜.d j := by exact_mod_cast hd
  have hne0 : (1 : ℚ) / 𝓜.d j ≠ 0 := by positivity
  have hne1 : (1 : ℚ) / 𝓜.d j ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq (by linarith)]; intro h; linarith
  by_cases hψ : ψ.1 ∈ smallSet n
  · refine ⟨hψ, ?_⟩
    rw [faceTable_of_mem 𝓜 t j hψ] at h ⊢
    by_cases h0 : t ⟨ψ.1, hψ⟩ = 0
    · exact ⟨Or.inl h0, by rw [if_pos h0]; exact h0⟩
    · by_cases h1 : t ⟨ψ.1, hψ⟩ = 1
      · exact ⟨Or.inr h1, by rw [if_neg h0, if_pos h1]; exact h1⟩
      · rw [if_neg h0, if_neg h1] at h
        rcases h with h | h
        · exact absurd h hne0
        · exact absurd h hne1
  · exfalso
    rw [faceTable_of_not_mem 𝓜 t j hψ] at h
    rcases h with h | h
    · exact hne0 h
    · exact hne1 h

/-- The step `n → n+1`: the face table lies in the product face of `t`.
Source: none: infrastructure (`bli-finite` `faceProd`)
Kind: L
Fidelity: n/a -/
lemma faceTable_mem_faceProd_self (ht : t.InUnit) :
    faceTable 𝓜 t (n + 1) ∈ faceProd smallIndex 𝓜.d n t := by
  rw [mem_faceProd_iff]
  refine ⟨faceTable_mem_grid 𝓜 t (n + 1), fun φ hφ => ?_⟩
  rw [Table.restrict_apply]
  exact faceTable_of_zero_one 𝓜 t (n + 1) (ψ := ⟨φ.1, smallSet_mono (Nat.le_succ n) φ.2⟩) φ.2 hφ

/-- The step `j → j+1` (`d_j ≥ 2`): the next face table lies in the product face of this one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma faceTable_mem_faceProd_succ (hd : 2 ≤ 𝓜.d j) :
    faceTable 𝓜 t (j + 1) ∈ faceProd smallIndex 𝓜.d j (faceTable 𝓜 t j) := by
  rw [mem_faceProd_iff]
  refine ⟨faceTable_mem_grid 𝓜 t (j + 1), fun φ hφ => ?_⟩
  obtain ⟨hψ, h01, heq⟩ := faceTable_zero_or_one 𝓜 t j hd hφ
  rw [Table.restrict_apply, ← heq]
  exact faceTable_of_zero_one 𝓜 t (j + 1) (ψ := ⟨φ.1, smallSet_mono (Nat.le_succ j) φ.2⟩) hψ h01

end FaceTable

/-- The table `T` with the coordinate `σ'` set to `0`.
Source: mandate M9
Kind: D
Fidelity: n/a -/
def zeroAt {m : ℕ} (σ' : Sentence) (T : Table smallIndex m) : Table smallIndex m :=
  fun ψ => if ψ.1 = σ' then 0 else T ψ

/-- `zeroAt_mem_grid`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma zeroAt_mem_grid {𝓜 : Mesh} {m : ℕ} (σ' : Sentence) {T : Table smallIndex m}
    (hT : T ∈ grid smallIndex 𝓜.d m) : zeroAt σ' T ∈ grid smallIndex 𝓜.d m := by
  rw [mem_grid_iff] at hT ⊢; intro ψ
  unfold zeroAt
  split_ifs
  · exact zero_mem_gridVals _
  · exact hT ψ

/-- The last step `j → j+1` of the M9 path: zeroing a coordinate that is not a day-`n` coordinate
keeps the table in the product face of the previous face table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma zeroAt_faceTable_mem_faceProd (𝓜 : Mesh) {n : ℕ} (t : Table smallIndex n) (j : ℕ)
    (hd : 2 ≤ 𝓜.d j) {σ' : Sentence} (hσ' : σ' ∉ smallSet n) :
    zeroAt σ' (faceTable 𝓜 t (j + 1)) ∈ faceProd smallIndex 𝓜.d j (faceTable 𝓜 t j) := by
  rw [mem_faceProd_iff]
  refine ⟨zeroAt_mem_grid σ' (faceTable_mem_grid 𝓜 t (j + 1)), fun φ hφ => ?_⟩
  obtain ⟨hψ, h01, heq⟩ := faceTable_zero_or_one 𝓜 t j hd hφ
  rw [Table.restrict_apply]
  have hne : ¬ (φ.1 = σ') := fun (h : φ.1 = σ') => hσ' (h ▸ hψ)
  show (if φ.1 = σ' then 0 else faceTable 𝓜 t (j + 1) ⟨φ.1, _⟩) = _
  rw [if_neg hne, ← heq]
  exact faceTable_of_zero_one 𝓜 t (j + 1) (ψ := ⟨φ.1, smallSet_mono (Nat.le_succ j) φ.2⟩) hψ h01

/-- The path of tables for the positivity argument: `t` on day `n`, the face table with `σ'`
zeroed on day `m`, the face table elsewhere.
Source: mandate M9
Kind: D
Fidelity: n/a -/
def m9Path (𝓜 : Mesh) {n : ℕ} (t : Table smallIndex n) (σ' : Sentence) (m j : ℕ) :
    Table smallIndex j :=
  if h : j = n then t.castDay h.symm
  else if j = m then zeroAt σ' (faceTable 𝓜 t j)
  else faceTable 𝓜 t j

section M9Path

variable (𝓜 : Mesh) {n : ℕ} (t : Table smallIndex n) (σ' : Sentence) (m : ℕ)

/-- `m9Path` on day `n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma m9Path_n : m9Path 𝓜 t σ' m n = t := by
  unfold m9Path; rw [dif_pos rfl]; rfl

/-- `m9Path` on day `m`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma m9Path_m (h : m ≠ n) : m9Path 𝓜 t σ' m m = zeroAt σ' (faceTable 𝓜 t m) := by
  unfold m9Path; rw [dif_neg h, if_pos rfl]

/-- `m9Path` elsewhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma m9Path_other {j : ℕ} (h1 : j ≠ n) (h2 : j ≠ m) : m9Path 𝓜 t σ' m j = faceTable 𝓜 t j := by
  unfold m9Path; rw [dif_neg h1, if_neg h2]

/-- `m9Path` on a day equal to `m` (without rewriting the day index).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma m9Path_of_eq {j : ℕ} (h1 : j ≠ n) (h2 : j = m) :
    m9Path 𝓜 t σ' m j = zeroAt σ' (faceTable 𝓜 t j) := by
  unfold m9Path; rw [dif_neg h1, if_pos h2]

end M9Path

/-- **`e2x_full_scope_fails` — `bli-found`'s full-scope constraint 2 is false for the tent
instance** (Known issue 1). Source: Appendix B's unrestricted "`φ`" at `main.tex:432`;
`bli-found`'s scope `Sminus m m` (the Notion reading: "no info about market states later than
`m`"), which admits a state atom of an intermediate day once it is small. Reading fixed: the
predicate `E2x (bliStateSystem Q 𝓜 c) (bliHistory Q 𝓜 tentSkeleton c)` as `bli-found` defines
it. Refutation: from **any** base with day-`n` prices in the unit cube (coherent bases
included — repair round 1; the round-0 statement asked for interior prices and so excluded
every base pricing `⊥` at `0`) and `2 ≤ d_{n+1}`, the day-`(n+1)` candidate `q'` coding the
face table `Q'` of `t = actualTable Q n` gives `σ' := stateAtom (n+1) q'`, small from day
`tokenSize σ'`; on `m := max (n+2) (tokenSize σ')` the candidate `q` coding the day-`m` face
table with `σ'` sent to `0` makes constraint 2 say `𝐏_n(σ' ⋏ σ_{m,q}) = 0`, while the chain
through the face tables (each in the product face of the previous one, `tentLaw_pos_iff`) has
positive tent mass. Surviving neighbour: the scoped predicate (`Lemmas.bli_cond2_scoped`). The
full-scope bundle itself is consistent (`recipe_isBLI_Roman`): what is refuted is its
conjunction with a Markov prior.
Source: Appendix B (`main.tex:432`); `bli-found` `E2x`; mandate M9
Kind: P
Fidelity: exact (refutation of the full-scope predicate for the tent instance)
Hyps: (a) day-`n` prices in `[0, 1]` (`ofBeliefStates_inUnit` for FAF markets); (a) `2 ≤ d_{n+1}` -/
theorem e2x_full_scope_fails {𝓜 : Mesh} (c : StateCoding 𝓜) (Q : RatHistory) (n : ℕ)
    (hQn : ∀ φ ∈ smallSet n, 0 ≤ Q n φ ∧ Q n φ ≤ 1) (hd : 2 ≤ 𝓜.d (n + 1)) :
    ¬ E2x (bliStateSystem Q 𝓜 c) (bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c) := by
  intro hE2
  set sk := tentSkeleton smallIndex 𝓜 with hsk
  set t := actualTable smallIndex Q n with ht
  have htu : t.InUnit := fun φ => hQn φ.1 φ.2
  have hdj : ∀ j, n + 1 ≤ j → 2 ≤ 𝓜.d j := fun j hj => hd.trans (mesh_d_mono 𝓜 hj)
  set Q' := faceTable 𝓜 t (n + 1) with hQ'
  have hQ'grid := faceTable_mem_grid 𝓜 t (n + 1)
  set q' := c.code (n + 1) Q' with hq'
  have hq'mem : q' ∈ c.states (n + 1) := c.code_mem_states hQ'grid
  set σ' := stateAtom (n + 1) q' with hσ'
  have hσ'large : σ' ∉ smallSet n := fun h =>
    not_smallOn_stateAtom c (Nat.lt_succ_self n) hq'mem (mem_smallSet.mp h)
  set m := max (n + 2) (tokenSize σ') with hm
  have hn2 : n + 2 ≤ m := le_max_left _ _
  have hnm : n + 1 < m := by omega
  have hσ'small : σ' ∈ smallSet m := by
    rw [mem_smallSet]
    exact (smallOn_tokenSize σ').mono (le_max_right _ _)
  have hσ'S : σ' ∈ Sminus m m := by
    rw [mem_Sminus]
    refine ⟨mem_smallSet.mp hσ'small, fun a ha => ?_⟩
    rw [atomDay_stateAtom (n + 1) q' a ha]; omega
  set Qm := zeroAt σ' (faceTable 𝓜 t m) with hQm
  have hQmgrid : Qm ∈ grid smallIndex 𝓜.d m := zeroAt_mem_grid σ' (faceTable_mem_grid 𝓜 t m)
  set q := c.code m Qm with hq
  have hqmem : q ∈ c.states m := c.code_mem_states hQmgrid
  have h := hE2 n m (by omega) q (by simpa using hqmem) σ' hσ'S
  have hval : (bliStateSystem Q 𝓜 c).val m q σ' = 0 := by
    rw [bliStateSystem_val, c.tableVal_code hQmgrid hσ'small, hQm]
    simp [zeroAt]
  rw [hval, zero_mul] at h
  have hpos : 0 < bliHistory Q 𝓜 sk c n (σ' ⋏ stateAtom m q) := by
    unfold bliHistory
    rw [bliPrice_of_tierA
        (not_smallOn_and_of_left (not_smallOn_stateAtom c (Nat.lt_succ_self n) hq'mem))
        (tierA_stateAtom_and_stateAtom c (Nat.lt_succ_self n) hq'mem (by omega) hqmem),
      tierAPrice_of_consistent c sk _ (consistent_pair_of_ne (by omega)), smallFactor_none, mul_one]
    unfold chainMass
    rw [latestEntry_pair_of_lt hnm]
    show (0 : ℝ) < ((chainProbH sk c [(n + 1, q'), (m, q)] n t (m - n) : ℚ) : ℝ)
    rw [Rat.cast_pos]
    have hm_ne : m ≠ n := by omega
    have hpath := chainProbH_pos_of_path c sk [(n + 1, q'), (m, q)] (m9Path 𝓜 t σ' m) (m - n) n
      ?_ ?_ ?_
    · rwa [m9Path_n 𝓜 t σ' m] at hpath
    · intro j hj hjm
      have hjm' : j < m := by omega
      show 0 < tentLaw 𝓜 j (m9Path 𝓜 t σ' m j) (m9Path 𝓜 t σ' m (j + 1))
      rcases Nat.eq_or_lt_of_le hj with rfl | hj'
      · -- the step `n → n+1`
        rw [m9Path_n, m9Path_other 𝓜 t σ' m (by omega) (by omega), tentLaw_pos_iff htu]
        exact faceTable_mem_faceProd_self 𝓜 t htu
      · rw [m9Path_other 𝓜 t σ' m (by omega) hjm'.ne, tentLaw_pos_iff (faceTable_inUnit 𝓜 t j)]
        by_cases hjm1 : j + 1 = m
        · -- the last step, into the zeroed face table
          rw [m9Path_of_eq 𝓜 t σ' m (by omega) hjm1]
          exact zeroAt_faceTable_mem_faceProd 𝓜 t j (hdj j hj') hσ'large
        · rw [m9Path_other 𝓜 t σ' m (by omega) hjm1]
          exact faceTable_mem_faceProd_succ 𝓜 t j (hdj j hj')
    · intro j hj hjm
      by_cases hjm1 : j = m
      · rw [hjm1, m9Path_m 𝓜 t σ' m hm_ne]; exact hQmgrid
      · rw [m9Path_other 𝓜 t σ' m (by omega) hjm1]; exact faceTable_mem_grid 𝓜 t j
    · intro j hj hjm x hx hxj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · simp only at hxj
        subst hxj
        rw [m9Path_other 𝓜 t σ' m (by omega) hnm.ne]
      · simp only at hxj
        subst hxj
        rw [m9Path_m 𝓜 t σ' m hm_ne]
  rw [h] at hpos
  exact lt_irrefl _ hpos

/-- The round-0 form of M9, as a corollary: interior day-`n` prices imply the unit-cube
hypothesis. Kept so that the round-0 statement remains available by name.
Source: mandate M9 (round-0 statement)
Kind: C
Fidelity: weaker: needs interior prices (excludes coherent bases); see `e2x_full_scope_fails`
Hyps: (a) interior day-`n` prices; (a) `2 ≤ d_{n+1}` -/
theorem e2x_full_scope_fails_of_interior {𝓜 : Mesh} (c : StateCoding 𝓜) (Q : RatHistory) (n : ℕ)
    (hint : ∀ φ ∈ smallSet n, 0 < Q n φ ∧ Q n φ < 1) (hd : 2 ≤ 𝓜.d (n + 1)) :
    ¬ E2x (bliStateSystem Q 𝓜 c) (bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c) :=
  e2x_full_scope_fails c Q n (fun φ hφ => ⟨(hint φ hφ).1.le, (hint φ hφ).2.le⟩) hd

/-! ## Known issue 2 — `TB` on every sentence fails for B1 at a Tier-B sentence -/

/-- The constant-`½` rational base.
Source: mandate Known issue 2
Kind: D
Fidelity: n/a -/
def halfBase : RatHistory := fun _ _ => 1 / 2

/-- `combine` with a failed left parse fails.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma combine_none_left' (b : Option (List (ℕ × ℕ) × Option Sentence)) : combine none b = none := by
  cases b <;> rfl

/-- An implication containing a future candidate atom is Tier B.
Source: mandate D2
Kind: L
Fidelity: n/a -/
lemma parse_imp_eq_none {𝓜 : Mesh} (c : StateCoding 𝓜) {n : ℕ} {φ χ : Sentence}
    (h : hasFutureAtom c n (φ 🡒 χ) = true) : parse c n (φ 🡒 χ) = none := by
  have h' : hasFutureAtom c n (Formula.imp φ χ) = true := h
  show parse c n (Formula.imp φ χ) = none
  unfold parse
  rw [if_pos h']

/-- **`tb_refuted_at` — `TB` on every sentence is false for B1, at day `n`** (Known issue 2). Source:
bli-slides-048 ("constraint 5 for every sentence"); `bli-found`'s `TB`. Reading fixed: `TB S P`
for the tent instance over the constant-`½` base. Refutation at the Tier-B sentence
`ψ := ∼stateAtom (n+2) q₀`: `𝐏_{n+1}(ψ)` and `𝐏_n(ψ ⋏ σ)` are both the base's `½`, so `TB`
would force `𝐏_n(σ) = 1`, but the tent law from the interior table `½` charges a second grid
point. Surviving neighbours: `TB_on` Tier A on the denominator grid (`Update.bli_TB_on_tierA`)
and the small-sentence ratio form (`Update.bli_update_small_ratio`). Ledger grade N−: a
constant base, one Tier-B sentence.
Source: bli-slides-048; `bli-found` `TB`; mandate Known issue 2
Kind: N−
Fidelity: exact (refutation of `TB` for B1)
Hyps: (a) none -/
theorem tb_refuted_at (𝓜 : Mesh) (c : StateCoding 𝓜) (n : ℕ) :
    ¬ TB (bliStateSystem halfBase 𝓜 c) (bliHistory halfBase 𝓜 (tentSkeleton smallIndex 𝓜) c) := by
  intro hTB
  set sk := tentSkeleton smallIndex 𝓜 with hsk
  have hZ : (fun _ => (0 : ℚ) : Table smallIndex (n + 2)) ∈ grid smallIndex 𝓜.d (n + 2) :=
    mem_grid_iff.mpr fun _ => zero_mem_gridVals _
  set q₀ := c.code (n + 2) (fun _ => 0) with hq₀
  have hq₀mem : q₀ ∈ c.states (n + 2) := c.code_mem_states hZ
  set ψ : Sentence := stateAtom (n + 2) q₀ 🡒 ⊥ with hψ
  have hfut1 : hasFutureAtom c (n + 1) ψ = true := by
    rw [hψ, hasFutureAtom_imp, hasFutureAtom_stateAtom, decide_eq_true ⟨by omega, hq₀mem⟩]
    simp
  have hfut0 : hasFutureAtom c n ψ = true := hasFutureAtom_of_succ c hfut1
  have hlarge1 : ¬ SmallOn (n + 1) ψ := not_smallOn_of_hasFutureAtom c hfut1
  have htB1 : tierA c (n + 1) ψ = none := by
    unfold tierA; rw [parse_imp_eq_none c hfut1]
  -- the realized state
  have hA : actualState smallIndex 𝓜.d halfBase (n + 1) ∈ grid smallIndex 𝓜.d (n + 1) :=
    actualState_mem_grid
  set A := actualState smallIndex 𝓜.d halfBase (n + 1) with hAdef
  set a := c.code (n + 1) A with hadef
  have hamem : a ∈ c.states (n + 1) := c.code_mem_states hA
  have hfutand : hasFutureAtom c n (ψ ⋏ stateAtom (n + 1) a) = true := by
    rw [hasFutureAtom_and, hfut0]; rfl
  have htBand : tierA c n (ψ ⋏ stateAtom (n + 1) a) = none := by
    unfold tierA
    rw [parse_and_def, if_pos hfutand, parse_imp_eq_none c hfut0, combine_none_left']
  have h1 : bliHistory halfBase 𝓜 sk c (n + 1) ψ = 1 / 2 := by
    unfold bliHistory
    rw [bliPrice_of_tierB hlarge1 htB1]; simp [halfBase]
  have h2 : bliHistory halfBase 𝓜 sk c n (ψ ⋏ stateAtom (n + 1) a) = 1 / 2 := by
    unfold bliHistory
    rw [bliPrice_of_tierB (not_smallOn_of_hasFutureAtom c hfutand) htBand]; simp [halfBase]
  have h3 : bliHistory halfBase 𝓜 sk c n (stateAtom (n + 1) a) =
      ((tentLaw 𝓜 n (actualTable smallIndex halfBase n) A : ℚ) : ℝ) := by
    unfold bliHistory
    rw [bliPrice_state c sk halfBase n hA]; rfl
  have hTBn := hTB n ψ
  simp only [bliStateSystem_actual] at hTBn
  rw [h1, h2, h3] at hTBn
  -- the tent mass at `A` is below one
  have htint : ∀ φ, 0 < actualTable smallIndex halfBase n φ ∧ actualTable smallIndex halfBase n φ < 1 :=
    fun _ => by simp [BliFinite.actualTable, halfBase]; norm_num
  set B : Table smallIndex (n + 1) := fun φ => if A φ = 0 then 1 else 0 with hBdef
  have hBgrid : B ∈ grid smallIndex 𝓜.d (n + 1) := by
    rw [mem_grid_iff]; intro φ
    simp only [hBdef]
    split_ifs
    · exact one_mem_gridVals (𝓜.d_pos _)
    · exact zero_mem_gridVals _
  have hBA : B ≠ A := by
    intro hBA
    have := congrFun hBA ⟨⊥, falsum_mem_smallSet (n + 1)⟩
    simp only [hBdef] at this
    split_ifs at this with h0
    · rw [h0] at this; exact one_ne_zero this
    · exact h0 this.symm
  have hBpos : 0 < tentLaw 𝓜 n (actualTable smallIndex halfBase n) B :=
    tentLaw_pos_of_interior htint hBgrid
  have hsum := tentLaw_sum_one (𝓜 := 𝓜) (actualTable smallIndex halfBase n)
  have hpair : tentLaw 𝓜 n (actualTable smallIndex halfBase n) A +
      tentLaw 𝓜 n (actualTable smallIndex halfBase n) B ≤ 1 := by
    rw [← hsum, ← Finset.sum_pair hBA.symm]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun Q _ _ => tentLaw_nonneg _ Q)
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hA
    · exact hBgrid
  have hlt : tentLaw 𝓜 n (actualTable smallIndex halfBase n) A < 1 := by linarith
  have hlt' : ((tentLaw 𝓜 n (actualTable smallIndex halfBase n) A : ℚ) : ℝ) < 1 := by
    exact_mod_cast hlt
  linarith

/-- **`tb_refuted` — `TB` on every sentence is false for B1** (Known issue 2), the day-free
statement of `tb_refuted_at` (audit r1 fidelity N11: the counterexample day is a parameter of
the proof, not of the claim).
Source: bli-slides-048; `bli-found` `TB`; mandate Known issue 2
Kind: N−
Fidelity: exact (refutation of `TB` for B1)
Hyps: (a) none -/
theorem tb_refuted (𝓜 : Mesh) (c : StateCoding 𝓜) :
    ¬ TB (bliStateSystem halfBase 𝓜 c) (bliHistory halfBase 𝓜 (tentSkeleton smallIndex 𝓜) c) :=
  tb_refuted_at 𝓜 c 0

/-! ## Concrete instances (audit r1 adversarial N9): the N+ and M9 at one point -/

/-- The constant-`½` base lies in the unit cube.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma halfBase_unit : ∀ n φ, 0 ≤ halfBase n φ ∧ halfBase n φ ≤ 1 := by
  intro n φ; simp only [halfBase]; norm_num

/-- **The N+ at a concrete point**: over `halfBase` and any mesh, on every day two distinct
day-`(n+1)` candidates carry positive superbelief (`bliHistory_tent_two_states` at `φ := ⊥`,
which `halfBase` prices at `½`). The hypothesis package of the N+ row is inhabited here, not
just asserted (`halfBase` is an incoherent base — it prices `⊥` at `½` — which is what makes
`⊥` an interior coordinate; the row's own hypothesis is any interior small price).
Source: mandate M3 (the package's N+); audit r1 adversarial N9
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem bliHistory_tent_two_states_halfBase (𝓜 : Mesh) (c : StateCoding 𝓜) (n : ℕ) :
    ∃ q₁ ∈ c.states (n + 1), ∃ q₂ ∈ c.states (n + 1), q₁ ≠ q₂ ∧
      0 < superbelief (bliHistory halfBase 𝓜 (tentSkeleton smallIndex 𝓜) c) n q₁ ∧
      0 < superbelief (bliHistory halfBase 𝓜 (tentSkeleton smallIndex 𝓜) c) n q₂ :=
  bliHistory_tent_two_states c halfBase halfBase_unit n (falsum_mem_smallSet n)
    (by simp only [halfBase]; norm_num) (by simp only [halfBase]; norm_num)

/-- **M9 at a concrete point**: for `halfBase` and any mesh with `2 ≤ d_{n+1}`, the full-scope
`E2x` fails.
Source: mandate M9; audit r1 adversarial N9
Kind: N+
Fidelity: n/a
Hyps: (a) `2 ≤ d_{n+1}` -/
theorem e2x_full_scope_fails_halfBase (𝓜 : Mesh) (c : StateCoding 𝓜) (n : ℕ)
    (hd : 2 ≤ 𝓜.d (n + 1)) :
    ¬ E2x (bliStateSystem halfBase 𝓜 c) (bliHistory halfBase 𝓜 (tentSkeleton smallIndex 𝓜) c) :=
  e2x_full_scope_fails c halfBase n (fun φ _ => halfBase_unit n φ) hd

end

end Cleanroom.Bli.BliTrajectory
