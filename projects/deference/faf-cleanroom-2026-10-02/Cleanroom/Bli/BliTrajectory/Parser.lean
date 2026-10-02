import Cleanroom.Bli.BliTrajectory.Defs

/-!
# `bli-trajectory` · Parser: what the Tier-A parser recognises, and the forward chain probability

Infrastructure for `Lemmas.lean`/`Update.lean`/`Refutations.lean`: the exact parses of the
constraint shapes (a bare state atom, `φ ⋏ σ`, `σ ⋏ σ'`, `φ ⋏ (σ ⋏ σ')`, `stateConj l`,
`φ ⋏ stateConj l`, `ψ ⋏ σ` for Tier-A `ψ`), largeness of anything mentioning a future state
atom, `latestEntry`/`Consistent` facts, and the algebra of `chainProbH` (inert entries, the
restart/cons identity, bounds, the single-path lower bound). Nothing here is a headline.
-/

namespace Cleanroom.Bli.BliTrajectory

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite

open Classical

variable {𝓜 : Mesh} (c : StateCoding 𝓜)

/-! ## Syntactic facts -/

/-- `stateConj` on a cons.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateConj_cons (x : ℕ × ℕ) (xs : List (ℕ × ℕ)) :
    stateConj (x :: xs) = stateAtom x.1 x.2 ⋏ stateConj xs := rfl

/-- A state atom is not `⊤`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateAtom_ne_top (m q : ℕ) : stateAtom m q ≠ (⊤ : Sentence) := by
  unfold stateAtom freshAtom; intro h; cases h

/-- A conjunction is not `⊤`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma and_ne_top (φ ψ : Sentence) : (φ ⋏ ψ) ≠ (⊤ : Sentence) := by
  intro h; cases h

/-- A nonempty state chain is not `⊤`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateConj_ne_top {l : List (ℕ × ℕ)} (hl : l ≠ []) : stateConj l ≠ (⊤ : Sentence) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons x xs => rw [stateConj_cons]; exact and_ne_top _ _

/-- `stateAtom m q` is `Formula.atom` of its code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateAtom_eq_atom (m q : ℕ) :
    stateAtom m q = Formula.atom (freshAtomCode stateFamily (Nat.pair m q)) := rfl

/-! ## `hasFutureAtom`, `futureStateAtom`, `NoFutureState` -/

/-- `hasFutureAtom` on a conjunction.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma hasFutureAtom_and (n : ℕ) (φ ψ : Sentence) :
    hasFutureAtom c n (φ ⋏ ψ) = (hasFutureAtom c n φ || hasFutureAtom c n ψ) := rfl

/-- `hasFutureAtom` on a disjunction.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma hasFutureAtom_or (n : ℕ) (φ ψ : Sentence) :
    hasFutureAtom c n (φ ⋎ ψ) = (hasFutureAtom c n φ || hasFutureAtom c n ψ) := rfl

/-- `hasFutureAtom` on an implication.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma hasFutureAtom_imp (n : ℕ) (φ ψ : Sentence) :
    hasFutureAtom c n (φ 🡒 ψ) = (hasFutureAtom c n φ || hasFutureAtom c n ψ) := rfl

/-- `hasFutureAtom` on `⊤` is `false`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma hasFutureAtom_top (n : ℕ) : hasFutureAtom c n (⊤ : Sentence) = false := rfl

/-- `hasFutureAtom` on `⊥` is `false`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma hasFutureAtom_bot (n : ℕ) : hasFutureAtom c n (⊥ : Sentence) = false := rfl

/-- `hasFutureAtom` on a state atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma hasFutureAtom_stateAtom (n m q : ℕ) :
    hasFutureAtom c n (stateAtom m q) = decide (n < m ∧ q ∈ c.states m) := by
  rw [stateAtom_eq_atom]; simp [hasFutureAtom]

/-- On an atom, `hasFutureAtom` is `futureStateAtom.isSome`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma hasFutureAtom_atom (n a : ℕ) :
    hasFutureAtom c n (Formula.atom a) = (futureStateAtom c n (Formula.atom a)).isSome := by
  simp only [hasFutureAtom, futureStateAtom]
  cases stateData a with
  | none => rfl
  | some x =>
    obtain ⟨m, q⟩ := x
    by_cases h : n < m ∧ q ∈ c.states m <;> simp [h]

/-- `futureStateAtom` on a state atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma futureStateAtom_stateAtom (n m q : ℕ) :
    futureStateAtom c n (stateAtom m q) =
      if n < m ∧ q ∈ c.states m then some (m, q) else none := by
  rw [stateAtom_eq_atom]; simp [futureStateAtom]

/-- `futureStateAtom` is `some` only on state atoms of a later day with a candidate code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma futureStateAtom_eq_some {n : ℕ} {ψ : Sentence} {m q : ℕ}
    (h : futureStateAtom c n ψ = some (m, q)) :
    ψ = stateAtom m q ∧ n < m ∧ q ∈ c.states m := by
  cases ψ with
  | atom a =>
    simp only [futureStateAtom] at h
    revert h
    cases hs : stateData a with
    | none => intro h; cases h
    | some x =>
      obtain ⟨m', q'⟩ := x
      intro h
      dsimp only at h
      split_ifs at h with hc
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨atom_eq_stateAtom_of_stateData hs, hc⟩
  | falsum => cases h
  | and _ _ => cases h
  | or _ _ => cases h
  | imp _ _ => cases h

/-- `futureStateAtom` is monotone in the day (later-day atoms are future for earlier days).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma futureStateAtom_of_succ {n : ℕ} {ψ : Sentence} {x : ℕ × ℕ}
    (h : futureStateAtom c (n + 1) ψ = some x) : futureStateAtom c n ψ = some x := by
  obtain ⟨m, q⟩ := x
  obtain ⟨rfl, hm, hq⟩ := futureStateAtom_eq_some c h
  rw [futureStateAtom_stateAtom, if_pos ⟨by omega, hq⟩]

/-- `hasFutureAtom` is antitone in the day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma hasFutureAtom_of_succ {n : ℕ} : ∀ {ψ : Sentence},
    hasFutureAtom c (n + 1) ψ = true → hasFutureAtom c n ψ = true
  | .atom a, h => by
    rw [hasFutureAtom_atom] at h ⊢
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    rw [futureStateAtom_of_succ c hx]; rfl
  | .falsum, h => by cases h
  | .and φ ψ, h => by
    simp only [hasFutureAtom, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (hasFutureAtom_of_succ h)
    · exact Or.inr (hasFutureAtom_of_succ h)
  | .or φ ψ, h => by
    simp only [hasFutureAtom, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (hasFutureAtom_of_succ h)
    · exact Or.inr (hasFutureAtom_of_succ h)
  | .imp φ ψ, h => by
    simp only [hasFutureAtom, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (hasFutureAtom_of_succ h)
    · exact Or.inr (hasFutureAtom_of_succ h)

/-- `NoFutureState` at a later day follows from `NoFutureState` at an earlier one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma NoFutureState.succ {n : ℕ} {ψ : Sentence} (h : NoFutureState c n ψ) :
    NoFutureState c (n + 1) ψ := by
  unfold NoFutureState at h ⊢
  by_contra h'
  rw [Bool.not_eq_false] at h'
  rw [hasFutureAtom_of_succ c h'] at h
  cases h

/-- `NoFutureState` on a conjunction.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma noFutureState_and_iff {n : ℕ} {φ ψ : Sentence} :
    NoFutureState c n (φ ⋏ ψ) ↔ NoFutureState c n φ ∧ NoFutureState c n ψ := by
  unfold NoFutureState; simp

/-! ## Largeness of anything mentioning a future state atom -/

/-- A conjunction is at least as large as either conjunct.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma not_smallOn_and_of_right {n : ℕ} {φ ψ : Sentence} (h : ¬ SmallOn n ψ) :
    ¬ SmallOn n (φ ⋏ ψ) := by
  unfold SmallOn at h ⊢; rw [tokenSize_and]; omega

/-- `not_smallOn_and_of_left`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma not_smallOn_and_of_left {n : ℕ} {φ ψ : Sentence} (h : ¬ SmallOn n φ) :
    ¬ SmallOn n (φ ⋏ ψ) := by
  unfold SmallOn at h ⊢; rw [tokenSize_and]; omega

/-- **Anything mentioning a future state atom (candidate code) is large.** The coding's `large`
field through `stateAtom_large`, propagated through the connectives by `tokenSize`.
Source: mandate D1/D2 (`large` used wherever a future atom must miss the small case)
Kind: L
Fidelity: exact -/
lemma not_smallOn_of_hasFutureAtom {n : ℕ} : ∀ {ψ : Sentence},
    hasFutureAtom c n ψ = true → ¬ SmallOn n ψ
  | .atom a, h => by
    rw [hasFutureAtom_atom] at h
    obtain ⟨⟨m, q⟩, hx⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨heq, hm, hq⟩ := futureStateAtom_eq_some c hx
    rw [heq]
    exact c.stateAtom_large_of_mem hq n hm.le
  | .falsum, h => by cases h
  | .and φ ψ, h => by
    simp only [hasFutureAtom, Bool.or_eq_true] at h
    rcases h with h | h
    · exact not_smallOn_and_of_left (not_smallOn_of_hasFutureAtom h)
    · exact not_smallOn_and_of_right (not_smallOn_of_hasFutureAtom h)
  | .or φ ψ, h => by
    simp only [hasFutureAtom, Bool.or_eq_true] at h
    change ¬ SmallOn n (φ ⋎ ψ)
    unfold SmallOn
    rw [tokenSize_or]
    rcases h with h | h
    · have := not_smallOn_of_hasFutureAtom h; unfold SmallOn at this; omega
    · have := not_smallOn_of_hasFutureAtom h; unfold SmallOn at this; omega
  | .imp φ ψ, h => by
    simp only [hasFutureAtom, Bool.or_eq_true] at h
    change ¬ SmallOn n (φ 🡒 ψ)
    unfold SmallOn
    rw [tokenSize_imp]
    rcases h with h | h
    · have := not_smallOn_of_hasFutureAtom h; unfold SmallOn at this; omega
    · have := not_smallOn_of_hasFutureAtom h; unfold SmallOn at this; omega

/-- A day-`n`-small sentence mentions no future state atom.
Source: mandate D1 (consequence of `large`)
Kind: L
Fidelity: exact -/
lemma noFutureState_of_smallOn {n : ℕ} {ψ : Sentence} (h : SmallOn n ψ) : NoFutureState c n ψ := by
  unfold NoFutureState
  by_contra h'
  rw [Bool.not_eq_false] at h'
  exact not_smallOn_of_hasFutureAtom c h' h

/-- A candidate's state atom of a later day is large on day `n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma not_smallOn_stateAtom {n m q : ℕ} (hnm : n < m) (hq : q ∈ c.states m) :
    ¬ SmallOn n (stateAtom m q) :=
  c.stateAtom_large_of_mem hq n hnm.le

/-! ## Parses of the constraint shapes -/

/-- `parse` on a conjunction (definitional).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma parse_and_def (n : ℕ) (φ χ : Sentence) :
    parse c n (φ ⋏ χ) =
      if hasFutureAtom c n (φ ⋏ χ) then
        combine (parse c n φ)
          (if χ = ⊤ ∧ (futureStateAtom c n φ).isSome then some ([], none) else parse c n χ)
      else some ([], some (φ ⋏ χ)) := rfl

/-- A sentence with no future state atom is an opaque small part.
Source: mandate D2
Kind: L
Fidelity: n/a -/
lemma parse_of_noFutureState {n : ℕ} : ∀ {ψ : Sentence}, NoFutureState c n ψ →
    parse c n ψ = some ([], some ψ)
  | .atom a, h => by
    unfold NoFutureState at h
    rw [hasFutureAtom_atom, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
    simp [parse, h]
  | .falsum, _ => rfl
  | .and φ ψ, h => by
    unfold NoFutureState at h
    simp only [parse, h, Bool.false_eq_true, if_false]
  | .or φ ψ, h => by
    unfold NoFutureState at h
    simp only [parse, h, Bool.false_eq_true, if_false]
  | .imp φ ψ, h => by
    unfold NoFutureState at h
    simp only [parse, h, Bool.false_eq_true, if_false]

/-- A future state atom parses as a one-element chain.
Source: mandate D2
Kind: L
Fidelity: n/a -/
lemma parse_stateAtom {n m q : ℕ} (hnm : n < m) (hq : q ∈ c.states m) :
    parse c n (stateAtom m q) = some ([(m, q)], none) := by
  rw [stateAtom_eq_atom]
  simp [parse, futureStateAtom, hnm, hq]

/-- `combine` on two parses, the left one with no small part.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma combine_none_left (l₁ l₂ : List (ℕ × ℕ)) (s : Option Sentence) :
    combine (some (l₁, none)) (some (l₂, s)) = some (l₁ ++ l₂, s) := by
  cases s <;> rfl

/-- `combine` on two parses, the right one with no small part.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma combine_some_none (l₁ l₂ : List (ℕ × ℕ)) (φ : Sentence) :
    combine (some (l₁, some φ)) (some (l₂, none)) = some (l₁ ++ l₂, some φ) := rfl

/-- `combine` with two small parts fails.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma combine_some_some (l₁ l₂ : List (ℕ × ℕ)) (φ ψ : Sentence) :
    combine (some (l₁, some φ)) (some (l₂, some ψ)) = none := rfl

/-- Inversion of `combine = some`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma combine_eq_some {a b : Option (List (ℕ × ℕ) × Option Sentence)} {l : List (ℕ × ℕ)}
    {s : Option Sentence} (h : combine a b = some (l, s)) :
    ∃ l₁ s₁ l₂ s₂, a = some (l₁, s₁) ∧ b = some (l₂, s₂) ∧ l = l₁ ++ l₂ ∧
      ((s₁ = none ∧ s = s₂) ∨ (s₂ = none ∧ s = s₁)) := by
  rcases a with _ | ⟨l₁, _ | φ⟩ <;> rcases b with _ | ⟨l₂, _ | ψ⟩ <;>
    simp only [combine, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  · exact ⟨l₁, none, l₂, none, rfl, rfl, h.1.symm, Or.inl ⟨rfl, h.2.symm⟩⟩
  · exact ⟨l₁, none, l₂, some ψ, rfl, rfl, h.1.symm, Or.inl ⟨rfl, h.2.symm⟩⟩
  · exact ⟨l₁, some φ, l₂, none, rfl, rfl, h.1.symm, Or.inr ⟨rfl, h.2.symm⟩⟩

/-- `parse` on a conjunction whose right conjunct is not `⊤`, from the conjuncts' parses.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma parse_and_of_parse {n : ℕ} {φ χ : Sentence} {l₁ l₂ : List (ℕ × ℕ)} {s₁ s₂ : Option Sentence}
    (h₁ : parse c n φ = some (l₁, s₁)) (h₂ : parse c n χ = some (l₂, s₂))
    (hfut : hasFutureAtom c n (φ ⋏ χ) = true) (hχ : χ ≠ ⊤) :
    parse c n (φ ⋏ χ) = combine (some (l₁, s₁)) (some (l₂, s₂)) := by
  rw [parse_and_def, if_pos hfut, h₁, if_neg (fun h => hχ h.1), h₂]

/-- `φ ⋏ σ` with `φ` mentioning no future state atom parses as `([(m, q)], some φ)`.
Source: mandate D2 (the `E2x` shape)
Kind: L
Fidelity: n/a -/
lemma parse_and_stateAtom {n m q : ℕ} (hnm : n < m) (hq : q ∈ c.states m) {φ : Sentence}
    (hφ : NoFutureState c n φ) :
    parse c n (φ ⋏ stateAtom m q) = some ([(m, q)], some φ) := by
  rw [parse_and_of_parse c (parse_of_noFutureState c hφ) (parse_stateAtom c hnm hq)
    (by rw [hasFutureAtom_and, hasFutureAtom_stateAtom, decide_eq_true ⟨hnm, hq⟩]; simp)
    (stateAtom_ne_top m q)]
  rfl

/-- `σ ⋏ σ'` parses as the two-element chain.
Source: mandate D2 (the `E5` shape)
Kind: L
Fidelity: n/a -/
lemma parse_stateAtom_and_stateAtom {n m o q₁ q₂ : ℕ} (hnm : n < m) (hq₁ : q₁ ∈ c.states m)
    (hno : n < o) (hq₂ : q₂ ∈ c.states o) :
    parse c n (stateAtom m q₁ ⋏ stateAtom o q₂) = some ([(m, q₁), (o, q₂)], none) := by
  rw [parse_and_of_parse c (parse_stateAtom c hnm hq₁) (parse_stateAtom c hno hq₂)
    (by rw [hasFutureAtom_and, hasFutureAtom_stateAtom, decide_eq_true ⟨hnm, hq₁⟩]; simp)
    (stateAtom_ne_top o q₂)]
  rfl

/-- `φ ⋏ (σ ⋏ σ')` parses as `([(m, q₁), (o, q₂)], some φ)`.
Source: mandate D2 (the `E3` shape)
Kind: L
Fidelity: n/a -/
lemma parse_and_two {n m o q₁ q₂ : ℕ} (hnm : n < m) (hq₁ : q₁ ∈ c.states m)
    (hno : n < o) (hq₂ : q₂ ∈ c.states o) {φ : Sentence} (hφ : NoFutureState c n φ) :
    parse c n (φ ⋏ (stateAtom m q₁ ⋏ stateAtom o q₂)) = some ([(m, q₁), (o, q₂)], some φ) := by
  have hfut : hasFutureAtom c n (φ ⋏ (stateAtom m q₁ ⋏ stateAtom o q₂)) = true := by
    rw [hasFutureAtom_and, hasFutureAtom_and, hasFutureAtom_stateAtom, decide_eq_true ⟨hnm, hq₁⟩]
    simp
  rw [parse_and_of_parse c (parse_of_noFutureState c hφ)
    (parse_stateAtom_and_stateAtom c hnm hq₁ hno hq₂) hfut (and_ne_top _ _)]
  rfl

/-- A nonempty chain of future candidate atoms parses as itself (the trailing `⊤` is neutral).
Source: mandate D2 (the `E3fin` shape)
Kind: L
Fidelity: n/a -/
lemma parse_stateConj {n : ℕ} : ∀ {l : List (ℕ × ℕ)}, l ≠ [] →
    (∀ x ∈ l, n < x.1 ∧ x.2 ∈ c.states x.1) → parse c n (stateConj l) = some (l, none)
  | [], hne, _ => absurd rfl hne
  | [x], _, hl => by
    have hx := hl x (List.mem_singleton_self x)
    rw [stateConj_cons]
    show parse c n (stateAtom x.1 x.2 ⋏ ⊤) = _
    have hfut : hasFutureAtom c n (stateAtom x.1 x.2 ⋏ ⊤) = true := by
      rw [hasFutureAtom_and, hasFutureAtom_stateAtom, decide_eq_true hx]; simp
    have htail : (⊤ : Sentence) = ⊤ ∧ (futureStateAtom c n (stateAtom x.1 x.2)).isSome :=
      ⟨rfl, by rw [futureStateAtom_stateAtom, if_pos hx]; rfl⟩
    rw [parse_and_def, if_pos hfut, if_pos htail, parse_stateAtom c hx.1 hx.2]
    rfl
  | x :: y :: ys, _, hl => by
    have hx := hl x (List.mem_cons_self)
    have ih := parse_stateConj (l := y :: ys) (List.cons_ne_nil _ _)
      (fun z hz => hl z (List.mem_cons_of_mem _ hz))
    have hfut : hasFutureAtom c n (stateAtom x.1 x.2 ⋏ stateConj (y :: ys)) = true := by
      rw [hasFutureAtom_and, hasFutureAtom_stateAtom, decide_eq_true hx]; simp
    rw [stateConj_cons, parse_and_of_parse c (parse_stateAtom c hx.1 hx.2) ih hfut
      (stateConj_ne_top (List.cons_ne_nil _ _))]
    rfl

/-- `φ ⋏ stateConj l` parses as `(l, some φ)`.
Source: mandate D2 (the `E3fin` shape)
Kind: L
Fidelity: n/a -/
lemma parse_and_stateConj {n : ℕ} {l : List (ℕ × ℕ)} (hne : l ≠ [])
    (hl : ∀ x ∈ l, n < x.1 ∧ x.2 ∈ c.states x.1) {φ : Sentence} (hφ : NoFutureState c n φ) :
    parse c n (φ ⋏ stateConj l) = some (l, some φ) := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hx := hl x (List.mem_cons_self)
  have hfut : hasFutureAtom c n (φ ⋏ stateConj (x :: xs)) = true := by
    rw [hasFutureAtom_and, stateConj_cons, hasFutureAtom_and, hasFutureAtom_stateAtom,
      decide_eq_true hx]
    simp
  rw [parse_and_of_parse c (parse_of_noFutureState c hφ) (parse_stateConj c hne hl) hfut
    (stateConj_ne_top hne)]
  rfl

/-! ## `latestEntry` and `Consistent` -/

/-- `latestEntry` on a cons (definitional).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma latestEntry_cons (x : ℕ × ℕ) (xs : List (ℕ × ℕ)) :
    latestEntry (x :: xs) = if (latestEntry xs).1 ≤ x.1 then x else latestEntry xs := rfl

/-- `latestEntry` of a singleton.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma latestEntry_singleton (x : ℕ × ℕ) : latestEntry [x] = x := by
  simp [latestEntry]

/-- `latestEntry` of an increasing pair is the second entry.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma latestEntry_pair_of_lt {m o q₁ q₂ : ℕ} (h : m < o) :
    latestEntry [(m, q₁), (o, q₂)] = (o, q₂) := by
  simp [latestEntry, not_le.mpr h]

/-- Every entry's day is at most the latest day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma le_latestEntry : ∀ {l : List (ℕ × ℕ)}, ∀ x ∈ l, x.1 ≤ (latestEntry l).1
  | [], x, hx => by simp at hx
  | y :: ys, x, hx => by
    rw [latestEntry_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · split_ifs with h
      · exact le_rfl
      · exact (not_le.mp h).le
    · have := le_latestEntry x hx
      split_ifs with h
      · exact this.trans h
      · exact this

/-- The latest entry of a nonempty chain is an entry.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma latestEntry_mem : ∀ {l : List (ℕ × ℕ)}, l ≠ [] → latestEntry l ∈ l
  | [], h => absurd rfl h
  | [x], _ => by rw [latestEntry_singleton]; exact List.mem_singleton_self x
  | x :: y :: ys, _ => by
    rw [latestEntry_cons]
    split_ifs
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (latestEntry_mem (List.cons_ne_nil _ _))

/-- In a strictly increasing chain the head's day is below every later day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma isChain_head_lt : ∀ {l : List (ℕ × ℕ)} {x : ℕ × ℕ},
    (x :: l).IsChain (fun a b => a.1 < b.1) → ∀ z ∈ l, x.1 < z.1
  | [], _, _, z, hz => by simp at hz
  | y :: ys, x, hc, z, hz => by
    have hxy : x.1 < y.1 := hc.rel_head
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hxy
    · exact hxy.trans (isChain_head_lt hc.tail z hz)

/-- The latest entry of a strictly increasing chain is its last entry.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma latestEntry_isChain : ∀ {l : List (ℕ × ℕ)} (hne : l ≠ []),
    l.IsChain (fun x y => x.1 < y.1) → latestEntry l = l.getLast hne
  | [], hne, _ => absurd rfl hne
  | [x], _, _ => by rw [latestEntry_singleton]; rfl
  | x :: y :: ys, _, hc => by
    have hxy : x.1 < y.1 := hc.rel_head
    have hy : y.1 ≤ (latestEntry (y :: ys)).1 := le_latestEntry y List.mem_cons_self
    rw [latestEntry_cons, if_neg (by omega), latestEntry_isChain (List.cons_ne_nil _ _) hc.tail]
    rfl

/-- The fold defining `latestEntry` does not depend on its initial value once every entry's day
dominates the initial day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma latestEntry_foldr_init : ∀ {l : List (ℕ × ℕ)} (y : ℕ × ℕ), l ≠ [] → (∀ x ∈ l, y.1 ≤ x.1) →
    l.foldr (fun x acc => if acc.1 ≤ x.1 then x else acc) y = latestEntry l
  | [], _, hne, _ => absurd rfl hne
  | [x], y, _, hy => by simp [latestEntry, hy x (List.mem_singleton_self x)]
  | x :: z :: zs, y, _, hy => by
    have ih := latestEntry_foldr_init (l := z :: zs) y (List.cons_ne_nil _ _)
      (fun w hw => hy w (List.mem_cons_of_mem _ hw))
    rw [List.foldr_cons, ih]; rfl

/-- Appending an entry whose day is at most every existing day leaves the latest entry unchanged.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma latestEntry_append_singleton {l : List (ℕ × ℕ)} (hne : l ≠ []) (y : ℕ × ℕ)
    (hy : ∀ x ∈ l, y.1 ≤ x.1) : latestEntry (l ++ [y]) = latestEntry l := by
  have h1 : latestEntry (l ++ [y]) = l.foldr (fun x acc => if acc.1 ≤ x.1 then x else acc) y := by
    unfold latestEntry; rw [List.foldr_append]; simp
  rw [h1]; exact latestEntry_foldr_init y hne hy

/-- A singleton is consistent.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma consistent_singleton (x : ℕ × ℕ) : Consistent [x] := by
  intro a ha b hb _
  rw [List.mem_singleton] at ha hb
  rw [ha, hb]

/-- A pair on distinct days is consistent.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma consistent_pair_of_ne {m o q₁ q₂ : ℕ} (h : m ≠ o) : Consistent [(m, q₁), (o, q₂)] := by
  intro a ha b hb hab
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exact absurd hab h
  · exact absurd hab.symm h
  · rfl

/-- A pair on one day with different codes is inconsistent (what `E5`'s exclusivity reads).
Source: mandate D2
Kind: L
Fidelity: n/a -/
lemma not_consistent_pair {m q₁ q₂ : ℕ} (h : q₁ ≠ q₂) : ¬ Consistent [(m, q₁), (m, q₂)] := by
  intro hc
  exact h (hc (m, q₁) (by simp) (m, q₂) (by simp) rfl)

/-- A strictly increasing chain is consistent.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma consistent_of_isChain : ∀ {l : List (ℕ × ℕ)}, l.IsChain (fun x y => x.1 < y.1) → Consistent l
  | [], _ => fun a ha => by simp at ha
  | x :: xs, hc => by
    have ih := consistent_of_isChain hc.tail
    have hlt := isChain_head_lt hc
    intro a ha b hb hab
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact absurd hab (ne_of_lt (hlt b hb'))
    · exact absurd hab.symm (ne_of_lt (hlt a ha'))
    · exact ih a ha' b hb' hab

/-- Appending an entry on a fresh day preserves and reflects consistency.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma consistent_append_singleton_iff {l : List (ℕ × ℕ)} {y : ℕ × ℕ} (hy : ∀ x ∈ l, x.1 ≠ y.1) :
    Consistent (l ++ [y]) ↔ Consistent l := by
  constructor
  · intro h a ha b hb hab
    exact h a (List.mem_append_left _ ha) b (List.mem_append_left _ hb) hab
  · intro h a ha b hb hab
    simp only [List.mem_append, List.mem_singleton] at ha hb
    rcases ha with ha | rfl <;> rcases hb with hb | rfl
    · exact h a ha b hb hab
    · exact absurd hab (hy a ha)
    · exact absurd hab.symm (hy b hb)
    · rfl

/-! ## `tierA` on the constraint shapes -/

/-- `tierA` from a parse with a nonempty chain and a small enough small part.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tierA_of_parse {n : ℕ} {ψ : Sentence} {l : List (ℕ × ℕ)} {s : Option Sentence}
    (h : parse c n ψ = some (l, s)) (hne : l ≠ []) (hs : SmallPart (latestEntry l).1 s) :
    tierA c n ψ = some (l, s) := by
  simp only [tierA, h]
  rw [if_pos ⟨hne, hs⟩]

/-- Inversion of `tierA = some`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tierA_eq_some {n : ℕ} {ψ : Sentence} {l : List (ℕ × ℕ)} {s : Option Sentence}
    (h : tierA c n ψ = some (l, s)) :
    parse c n ψ = some (l, s) ∧ l ≠ [] ∧ SmallPart (latestEntry l).1 s := by
  unfold tierA at h
  revert h
  cases hp : parse c n ψ with
  | none => intro h; cases h
  | some x =>
    obtain ⟨l', s'⟩ := x
    intro h
    dsimp only at h
    split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, hc⟩

/-- Every chain entry of a parse is a future candidate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma parse_entries {n : ℕ} : ∀ {ψ : Sentence} {l : List (ℕ × ℕ)} {s : Option Sentence},
    parse c n ψ = some (l, s) → ∀ x ∈ l, n < x.1 ∧ x.2 ∈ c.states x.1
  | .atom a, l, s, h => by
    unfold parse at h
    revert h
    cases hf : futureStateAtom c n (.atom a) with
    | some x =>
      intro h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro y hy
      rw [List.mem_singleton] at hy
      subst hy
      obtain ⟨m, q⟩ := y
      exact (futureStateAtom_eq_some c hf).2
    | none =>
      intro h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro y hy; simp at hy
  | .falsum, l, s, h => by
    unfold parse at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro y hy; simp at hy
  | .and φ χ, l, s, h => by
    change parse c n (φ ⋏ χ) = some (l, s) at h
    by_cases hf : hasFutureAtom c n (φ ⋏ χ) = true
    · rw [parse_and_def, if_pos hf] at h
      obtain ⟨l₁, s₁, l₂, s₂, h₁, h₂, rfl, -⟩ := combine_eq_some h
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact parse_entries h₁ x hx
      · by_cases htail : χ = ⊤ ∧ (futureStateAtom c n φ).isSome
        · rw [if_pos htail] at h₂
          simp only [Option.some.injEq, Prod.mk.injEq] at h₂
          rw [← h₂.1] at hx; simp at hx
        · rw [if_neg htail] at h₂
          exact parse_entries h₂ x hx
    · rw [parse_and_def, if_neg hf] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro y hy; simp at hy
  | .or φ χ, l, s, h => by
    by_cases hf : hasFutureAtom c n (Formula.or φ χ) = true
    · unfold parse at h; rw [if_pos hf] at h; cases h
    · unfold parse at h; rw [if_neg hf] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro y hy; simp at hy
  | .imp φ χ, l, s, h => by
    by_cases hf : hasFutureAtom c n (Formula.imp φ χ) = true
    · unfold parse at h; rw [if_pos hf] at h; cases h
    · unfold parse at h; rw [if_neg hf] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro y hy; simp at hy

/-- A bare future candidate atom is Tier A.
Source: mandate D2
Kind: L
Fidelity: n/a -/
lemma tierA_stateAtom {n m q : ℕ} (hnm : n < m) (hq : q ∈ c.states m) :
    tierA c n (stateAtom m q) = some ([(m, q)], none) :=
  tierA_of_parse c (parse_stateAtom c hnm hq) (List.cons_ne_nil _ _) trivial

/-- `φ ⋏ σ` is Tier A when `φ` mentions no future state atom and is small on `σ`'s day.
Source: mandate D2 (the `E2x` shape)
Kind: L
Fidelity: n/a -/
lemma tierA_and_stateAtom {n m q : ℕ} (hnm : n < m) (hq : q ∈ c.states m) {φ : Sentence}
    (hφ : NoFutureState c n φ) (hsmall : SmallOn m φ) :
    tierA c n (φ ⋏ stateAtom m q) = some ([(m, q)], some φ) :=
  tierA_of_parse c (parse_and_stateAtom c hnm hq hφ) (List.cons_ne_nil _ _)
    (by show SmallOn _ φ; rw [latestEntry_singleton]; exact hsmall)

/-- `σ ⋏ σ'` is Tier A.
Source: mandate D2 (the `E5` shape)
Kind: L
Fidelity: n/a -/
lemma tierA_stateAtom_and_stateAtom {n m o q₁ q₂ : ℕ} (hnm : n < m) (hq₁ : q₁ ∈ c.states m)
    (hno : n < o) (hq₂ : q₂ ∈ c.states o) :
    tierA c n (stateAtom m q₁ ⋏ stateAtom o q₂) = some ([(m, q₁), (o, q₂)], none) :=
  tierA_of_parse c (parse_stateAtom_and_stateAtom c hnm hq₁ hno hq₂) (List.cons_ne_nil _ _) trivial

/-- `φ ⋏ (σ ⋏ σ')` is Tier A.
Source: mandate D2 (the `E3` shape)
Kind: L
Fidelity: n/a -/
lemma tierA_and_two {n m o q₁ q₂ : ℕ} (hnm : n < m) (hq₁ : q₁ ∈ c.states m)
    (hno : n < o) (hq₂ : q₂ ∈ c.states o) (hmo : m < o) {φ : Sentence}
    (hφ : NoFutureState c n φ) (hsmall : SmallOn o φ) :
    tierA c n (φ ⋏ (stateAtom m q₁ ⋏ stateAtom o q₂)) = some ([(m, q₁), (o, q₂)], some φ) :=
  tierA_of_parse c (parse_and_two c hnm hq₁ hno hq₂ hφ) (List.cons_ne_nil _ _)
    (by show SmallOn _ φ; rw [latestEntry_pair_of_lt hmo]; exact hsmall)

/-- `stateConj l` is Tier A.
Source: mandate D2 (the `E3fin` shape)
Kind: L
Fidelity: n/a -/
lemma tierA_stateConj {n : ℕ} {l : List (ℕ × ℕ)} (hne : l ≠ [])
    (hl : ∀ x ∈ l, n < x.1 ∧ x.2 ∈ c.states x.1) : tierA c n (stateConj l) = some (l, none) :=
  tierA_of_parse c (parse_stateConj c hne hl) hne trivial

/-- `φ ⋏ stateConj l` is Tier A.
Source: mandate D2 (the `E3fin` shape)
Kind: L
Fidelity: n/a -/
lemma tierA_and_stateConj {n : ℕ} {l : List (ℕ × ℕ)} (hne : l ≠ [])
    (hl : ∀ x ∈ l, n < x.1 ∧ x.2 ∈ c.states x.1) {φ : Sentence} (hφ : NoFutureState c n φ)
    (hsmall : SmallOn (latestEntry l).1 φ) : tierA c n (φ ⋏ stateConj l) = some (l, some φ) :=
  tierA_of_parse c (parse_and_stateConj c hne hl hφ) hne hsmall

/-! ## The day-shift lemma (for the total update) -/

/-- **Day shift.** A parse at day `n+1` whose small part mentions no state atom of a day `> n` is
the same parse at day `n` (the only difference between the two days is the status of day-`(n+1)`
atoms, and the hypothesis excludes them from the small part).
Source: mandate M6 (the `ψ ⋏ σ` shape)
Kind: L
Fidelity: n/a -/
lemma parse_of_parse_succ {n : ℕ} : ∀ {ψ : Sentence} {l : List (ℕ × ℕ)} {s : Option Sentence},
    parse c (n + 1) ψ = some (l, s) → (∀ φ, s = some φ → NoFutureState c n φ) →
    parse c n ψ = some (l, s)
  | .atom a, l, s, h, hs => by
    unfold parse at h ⊢
    revert h
    cases hf : futureStateAtom c (n + 1) (.atom a) with
    | some x =>
      intro h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [futureStateAtom_of_succ c hf]
    | none =>
      intro h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := hs _ rfl
      unfold NoFutureState at this
      rw [hasFutureAtom_atom, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at this
      rw [this]
  | .falsum, l, s, h, _ => h
  | .and φ χ, l, s, h, hs => by
    change parse c (n + 1) (φ ⋏ χ) = some (l, s) at h
    show parse c n (φ ⋏ χ) = some (l, s)
    by_cases hf : hasFutureAtom c (n + 1) (φ ⋏ χ) = true
    · have hf0 : hasFutureAtom c n (φ ⋏ χ) = true := hasFutureAtom_of_succ c hf
      rw [parse_and_def, if_pos hf] at h
      rw [parse_and_def, if_pos hf0]
      obtain ⟨l₁, s₁, l₂, s₂, h₁, h₂, rfl, hss⟩ := combine_eq_some h
      rw [h₁, h₂] at h
      have ih₁ : parse c n φ = some (l₁, s₁) := by
        refine parse_of_parse_succ h₁ (fun φ' hφ' => ?_)
        rcases hss with ⟨h1, _⟩ | ⟨_, h2⟩
        · rw [h1] at hφ'; cases hφ'
        · exact hs φ' (h2.trans hφ')
      have htail_eq : (if χ = ⊤ ∧ (futureStateAtom c n φ).isSome then some ([], none)
          else parse c n χ) = some (l₂, s₂) := by
        by_cases htail : χ = ⊤ ∧ (futureStateAtom c (n + 1) φ).isSome
        · rw [if_pos htail] at h₂
          obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp htail.2
          rw [if_pos ⟨htail.1, by rw [futureStateAtom_of_succ c hx]; rfl⟩]
          exact h₂
        · rw [if_neg htail] at h₂
          have ih₂ : parse c n χ = some (l₂, s₂) := by
            refine parse_of_parse_succ h₂ (fun φ' hφ' => ?_)
            rcases hss with ⟨_, h1⟩ | ⟨h2, _⟩
            · exact hs φ' (h1.trans hφ')
            · rw [h2] at hφ'; cases hφ'
          by_cases htail0 : χ = ⊤ ∧ (futureStateAtom c n φ).isSome
          · exfalso
            obtain ⟨hχ, hφ⟩ := htail0
            obtain ⟨⟨m, q⟩, hx⟩ := Option.isSome_iff_exists.mp hφ
            obtain ⟨rfl, hm, hq⟩ := futureStateAtom_eq_some c hx
            have hnot : ¬ (n + 1 < m ∧ q ∈ c.states m) := fun h' =>
              htail ⟨hχ, by rw [futureStateAtom_stateAtom, if_pos h']; rfl⟩
            have hop : parse c (n + 1) (stateAtom m q) = some ([], some (stateAtom m q)) := by
              apply parse_of_noFutureState
              unfold NoFutureState
              rw [hasFutureAtom_stateAtom, decide_eq_false hnot]
            rw [hop] at h₁
            simp only [Option.some.injEq, Prod.mk.injEq] at h₁
            obtain ⟨_, hs₁⟩ := h₁
            subst hχ
            have hop2 : parse c (n + 1) (⊤ : Sentence) = some ([], some ⊤) :=
              parse_of_noFutureState c rfl
            rw [hop2] at h₂
            simp only [Option.some.injEq, Prod.mk.injEq] at h₂
            obtain ⟨_, hs₂⟩ := h₂
            rcases hss with ⟨h1, _⟩ | ⟨h2, _⟩
            · rw [← hs₁] at h1; cases h1
            · rw [← hs₂] at h2; cases h2
          · rw [if_neg htail0]; exact ih₂
      rw [ih₁, htail_eq]; exact h
    · rw [parse_and_def, if_neg hf] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact parse_of_noFutureState c (hs _ rfl)
  | .or φ χ, l, s, h, hs => by
    by_cases hf : hasFutureAtom c (n + 1) (Formula.or φ χ) = true
    · unfold parse at h; rw [if_pos hf] at h; cases h
    · unfold parse at h; rw [if_neg hf] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact parse_of_noFutureState c (hs _ rfl)
  | .imp φ χ, l, s, h, hs => by
    by_cases hf : hasFutureAtom c (n + 1) (Formula.imp φ χ) = true
    · unfold parse at h; rw [if_pos hf] at h; cases h
    · unfold parse at h; rw [if_neg hf] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact parse_of_noFutureState c (hs _ rfl)

/-! ## The forward chain probability -/

variable (sk : Skeleton smallIndex 𝓜.d)

/-- `chainProbH` at horizon `0` is `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma chainProbH_zero (l : List (ℕ × ℕ)) (n : ℕ) (t : Table smallIndex n) :
    chainProbH sk c l n t 0 = 1 := rfl

/-- The defining recursion of `chainProbH`, as a rewrite rule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainProbH_succ (l : List (ℕ × ℕ)) (n : ℕ) (t : Table smallIndex n) (H : ℕ) :
    chainProbH sk c l n t (H + 1) = ∑ Q ∈ grid smallIndex 𝓜.d (n + 1),
      (sk.κ n).law t Q *
        (if ∀ x ∈ l, x.1 = n + 1 → c.code (n + 1) Q = x.2 then chainProbH sk c l (n + 1) Q H
         else 0) := rfl

/-- `chainProbH` is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainProbH_nonneg (l : List (ℕ × ℕ)) :
    ∀ (H n : ℕ) (t : Table smallIndex n), 0 ≤ chainProbH sk c l n t H
  | 0, _, _ => zero_le_one
  | H + 1, n, t => by
    rw [chainProbH_succ]
    refine Finset.sum_nonneg fun Q _ => mul_nonneg ((sk.κ n).law_nonneg t Q) ?_
    split_ifs
    · exact chainProbH_nonneg l H (n + 1) Q
    · exact le_rfl

/-- `chainProbH` is at most one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainProbH_le_one (l : List (ℕ × ℕ)) :
    ∀ (H n : ℕ) (t : Table smallIndex n), chainProbH sk c l n t H ≤ 1
  | 0, _, _ => le_rfl
  | H + 1, n, t => by
    rw [chainProbH_succ]
    refine le_trans (Finset.sum_le_sum (g := fun Q => (sk.κ n).law t Q * 1) fun Q _ => ?_) ?_
    · refine mul_le_mul_of_nonneg_left ?_ ((sk.κ n).law_nonneg t Q)
      split_ifs
      · exact chainProbH_le_one l H (n + 1) Q
      · exact zero_le_one
    · simp only [mul_one]; exact ((sk.κ n).sum_law t).le

/-- `chainProbH` depends on the chain only through membership.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainProbH_congr_mem {l l' : List (ℕ × ℕ)} (h : ∀ x, x ∈ l ↔ x ∈ l') :
    ∀ (H n : ℕ) (t : Table smallIndex n), chainProbH sk c l n t H = chainProbH sk c l' n t H
  | 0, _, _ => rfl
  | H + 1, n, t => by
    rw [chainProbH_succ, chainProbH_succ]
    refine Finset.sum_congr rfl fun Q _ => ?_
    have hc : (∀ x ∈ l, x.1 = n + 1 → c.code (n + 1) Q = x.2) ↔
        (∀ x ∈ l', x.1 = n + 1 → c.code (n + 1) Q = x.2) := by
      constructor
      · intro hh x hx; exact hh x ((h x).mpr hx)
      · intro hh x hx; exact hh x ((h x).mp hx)
    rw [chainProbH_congr_mem h H (n + 1) Q]
    by_cases hl : ∀ x ∈ l, x.1 = n + 1 → c.code (n + 1) Q = x.2
    · rw [if_pos hl, if_pos (hc.mp hl)]
    · rw [if_neg hl, if_neg (fun h' => hl (hc.mpr h'))]

/-- An entry whose day is not after `n` is inert from day `n` on.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainProbH_cons_of_le {x : ℕ × ℕ} (l : List (ℕ × ℕ)) :
    ∀ (H n : ℕ) (t : Table smallIndex n), x.1 ≤ n →
      chainProbH sk c (x :: l) n t H = chainProbH sk c l n t H
  | 0, _, _, _ => rfl
  | H + 1, n, t, hx => by
    rw [chainProbH_succ, chainProbH_succ]
    refine Finset.sum_congr rfl fun Q _ => ?_
    have hc : (∀ y ∈ x :: l, y.1 = n + 1 → c.code (n + 1) Q = y.2) ↔
        (∀ y ∈ l, y.1 = n + 1 → c.code (n + 1) Q = y.2) := by
      constructor
      · intro hh y hy; exact hh y (List.mem_cons_of_mem _ hy)
      · intro hh y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · intro h1; omega
        · exact hh y hy
    rw [chainProbH_cons_of_le l H (n + 1) Q (by omega)]
    by_cases hl : ∀ y ∈ l, y.1 = n + 1 → c.code (n + 1) Q = y.2
    · rw [if_pos (hc.mpr hl), if_pos hl]
    · rw [if_neg (fun h' => hl (hc.mp h')), if_neg hl]

/-- A chain all of whose days are `≤ n` has probability `1` from day `n` (the kernels sum to one).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainProbH_of_all_le (l : List (ℕ × ℕ)) :
    ∀ (H n : ℕ) (t : Table smallIndex n), (∀ x ∈ l, x.1 ≤ n) → chainProbH sk c l n t H = 1
  | 0, _, _, _ => rfl
  | H + 1, n, t, hl => by
    rw [chainProbH_succ]
    have key : ∀ Q ∈ grid smallIndex 𝓜.d (n + 1),
        (sk.κ n).law t Q * (if ∀ x ∈ l, x.1 = n + 1 → c.code (n + 1) Q = x.2
          then chainProbH sk c l (n + 1) Q H else 0) = (sk.κ n).law t Q := by
      intro Q _
      rw [if_pos (fun x hx h1 => by have := hl x hx; omega),
        chainProbH_of_all_le l H (n + 1) Q (fun x hx => (hl x hx).trans (Nat.le_succ n)), mul_one]
    rw [Finset.sum_congr rfl key]
    exact (sk.κ n).sum_law t

/-- The empty chain has probability `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainProbH_nil (H n : ℕ) (t : Table smallIndex n) : chainProbH sk c [] n t H = 1 :=
  chainProbH_of_all_le c sk [] H n t (fun x hx => by simp at hx)

/-- **The restart identity** (the chain rule, built in): a chain whose first entry is the code
of a grid table `A` on day `n+1` (and whose other entries are later) has, from `t` on day `n`,
probability `κ_n(t)(A)` times the probability of the rest **restarted from `A`**.
Source: bli-soto-a-035 (chain rule); [[bli-program]] §3.5 (iii); mandate D2/M6
Kind: L
Fidelity: exact -/
lemma chainProbH_cons_succ {n : ℕ} {A : Table smallIndex (n + 1)}
    (hA : A ∈ grid smallIndex 𝓜.d (n + 1)) (l : List (ℕ × ℕ)) (hl : ∀ x ∈ l, n + 1 < x.1)
    (t : Table smallIndex n) (H : ℕ) :
    chainProbH sk c ((n + 1, c.code (n + 1) A) :: l) n t (H + 1) =
      (sk.κ n).law t A * chainProbH sk c l (n + 1) A H := by
  rw [chainProbH_succ]
  have key : ∀ Q ∈ grid smallIndex 𝓜.d (n + 1),
      (sk.κ n).law t Q *
        (if ∀ x ∈ (n + 1, c.code (n + 1) A) :: l, x.1 = n + 1 → c.code (n + 1) Q = x.2
          then chainProbH sk c ((n + 1, c.code (n + 1) A) :: l) (n + 1) Q H else 0)
        = if Q = A then (sk.κ n).law t A * chainProbH sk c l (n + 1) A H else 0 := by
    intro Q hQ
    by_cases hQA : Q = A
    · subst hQA
      rw [if_pos, if_pos rfl, chainProbH_cons_of_le c sk l H (n + 1) Q le_rfl]
      intro x hx h1
      rcases List.mem_cons.mp hx with rfl | hx
      · rfl
      · exact absurd h1 (by have := hl x hx; omega)
    · rw [if_neg, if_neg hQA, mul_zero]
      intro h
      have := h (n + 1, c.code (n + 1) A) List.mem_cons_self rfl
      exact hQA (c.inj (n + 1) hQ hA this)
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' (grid smallIndex 𝓜.d (n + 1)) A, if_pos hA]

/-- A one-element chain naming a grid table's code on day `n+1` has probability the kernel entry.
Source: mandate M1 (`bli_state`)
Kind: L
Fidelity: exact -/
lemma chainProbH_singleton_code {n : ℕ} {A : Table smallIndex (n + 1)}
    (hA : A ∈ grid smallIndex 𝓜.d (n + 1)) (t : Table smallIndex n) (H : ℕ) :
    chainProbH sk c [(n + 1, c.code (n + 1) A)] n t (H + 1) = (sk.κ n).law t A := by
  rw [chainProbH_cons_succ c sk hA [] (fun x hx => by simp at hx), chainProbH_nil, mul_one]

/-- A one-element chain naming a non-candidate code has probability `0`.
Source: mandate D2 ("a code outside `states m` prices `0`")
Kind: L
Fidelity: exact -/
lemma chainProbH_singleton_of_not_mem {n q : ℕ} (hq : q ∉ c.states (n + 1))
    (t : Table smallIndex n) (H : ℕ) : chainProbH sk c [(n + 1, q)] n t (H + 1) = 0 := by
  rw [chainProbH_succ]
  refine Finset.sum_eq_zero fun Q hQ => ?_
  rw [if_neg, mul_zero]
  intro h
  have hcq : c.code (n + 1) Q = q := h (n + 1, q) (List.mem_singleton_self _) rfl
  exact hq (hcq ▸ c.code_mem_states hQ)

/-- The single-term lower bound: one admissible next table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainProbH_succ_ge {n : ℕ} (l : List (ℕ × ℕ)) (t : Table smallIndex n) (H : ℕ)
    {Q₀ : Table smallIndex (n + 1)} (hQ₀ : Q₀ ∈ grid smallIndex 𝓜.d (n + 1))
    (hcond : ∀ x ∈ l, x.1 = n + 1 → c.code (n + 1) Q₀ = x.2) :
    (sk.κ n).law t Q₀ * chainProbH sk c l (n + 1) Q₀ H ≤ chainProbH sk c l n t (H + 1) := by
  rw [chainProbH_succ]
  have hnn : ∀ Q ∈ grid smallIndex 𝓜.d (n + 1),
      0 ≤ (sk.κ n).law t Q * (if ∀ x ∈ l, x.1 = n + 1 → c.code (n + 1) Q = x.2
        then chainProbH sk c l (n + 1) Q H else 0) := by
    intro Q _
    refine mul_nonneg ((sk.κ n).law_nonneg t Q) ?_
    split_ifs
    · exact chainProbH_nonneg c sk l H (n + 1) Q
    · exact le_rfl
  calc (sk.κ n).law t Q₀ * chainProbH sk c l (n + 1) Q₀ H
      = (sk.κ n).law t Q₀ * (if ∀ x ∈ l, x.1 = n + 1 → c.code (n + 1) Q₀ = x.2
          then chainProbH sk c l (n + 1) Q₀ H else 0) := by rw [if_pos hcond]
    _ ≤ ∑ Q ∈ grid smallIndex 𝓜.d (n + 1), (sk.κ n).law t Q *
          (if ∀ x ∈ l, x.1 = n + 1 → c.code (n + 1) Q = x.2
            then chainProbH sk c l (n + 1) Q H else 0) := Finset.single_le_sum hnn hQ₀

/-- **Path positivity**: a path of grid tables `T` through the chain's codes with positive
kernel steps gives positive chain probability (the mechanism of `Refutations.lean`).
Source: mandate M9
Kind: L
Fidelity: n/a -/
lemma chainProbH_pos_of_path (l : List (ℕ × ℕ)) (T : ∀ j, Table smallIndex j) :
    ∀ (H n : ℕ),
      (∀ j, n ≤ j → j < n + H → 0 < (sk.κ j).law (T j) (T (j + 1))) →
      (∀ j, n < j → j ≤ n + H → T j ∈ grid smallIndex 𝓜.d j) →
      (∀ j, n < j → j ≤ n + H → ∀ x ∈ l, x.1 = j → c.code j (T j) = x.2) →
      0 < chainProbH sk c l n (T n) H
  | 0, _, _, _, _ => zero_lt_one
  | H + 1, n, hpos, hgrid, hcode => by
    have h1 : 0 < (sk.κ n).law (T n) (T (n + 1)) := hpos n le_rfl (by omega)
    have h2 : 0 < chainProbH sk c l (n + 1) (T (n + 1)) H :=
      chainProbH_pos_of_path l T H (n + 1) (fun j hj hjH => hpos j (by omega) (by omega))
        (fun j hj hjH => hgrid j (by omega) (by omega))
        (fun j hj hjH => hcode j (by omega) (by omega))
    exact lt_of_lt_of_le (mul_pos h1 h2)
      (chainProbH_succ_ge c sk l (T n) H (hgrid (n + 1) (by omega) (by omega))
        (hcode (n + 1) (by omega) (by omega)))

/-- The chain mass of a one-element chain naming a grid table's code on day `n+1`.
Source: mandate M1 (`bli_state`)
Kind: L
Fidelity: exact -/
lemma chainMass_singleton_code {n : ℕ} {A : Table smallIndex (n + 1)}
    (hA : A ∈ grid smallIndex 𝓜.d (n + 1)) (t : Table smallIndex n) :
    chainMass sk c n t [(n + 1, c.code (n + 1) A)] = (sk.κ n).law t A := by
  unfold chainMass
  rw [latestEntry_singleton]
  show chainProbH sk c _ n t (n + 1 - n) = _
  rw [Nat.add_sub_cancel_left]
  exact chainProbH_singleton_code c sk hA t 0

/-- The chain mass is in `[0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainMass_mem_Icc (n : ℕ) (t : Table smallIndex n) (l : List (ℕ × ℕ)) :
    0 ≤ chainMass sk c n t l ∧ chainMass sk c n t l ≤ 1 :=
  ⟨chainProbH_nonneg c sk l _ n t, chainProbH_le_one c sk l _ n t⟩

/-! ## Unfolding the prices -/

/-- `smallFactor` with no small part.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma smallFactor_none (l : List (ℕ × ℕ)) : smallFactor c l none = 1 := rfl

/-- `smallFactor` with a small part.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma smallFactor_some (l : List (ℕ × ℕ)) (φ : Sentence) :
    smallFactor c l (some φ) = c.tableVal (latestEntry l).1 (latestEntry l).2 φ := rfl

/-- The small factor is in `[0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma smallFactor_mem_Icc (l : List (ℕ × ℕ)) (s : Option Sentence) :
    0 ≤ smallFactor c l s ∧ smallFactor c l s ≤ 1 := by
  cases s with
  | none => exact ⟨zero_le_one, le_rfl⟩
  | some φ => exact c.tableVal_mem_Icc _ _ _

/-- `tierAPrice` on a consistent chain.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tierAPrice_of_consistent {n : ℕ} (t : Table smallIndex n) {l : List (ℕ × ℕ)}
    (hc : Consistent l) (s : Option Sentence) :
    tierAPrice sk c n t (l, s) = chainMass sk c n t l * smallFactor c l s := by
  simp only [tierAPrice]; rw [if_pos hc]

/-- `tierAPrice` on an inconsistent chain is `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tierAPrice_of_not_consistent {n : ℕ} (t : Table smallIndex n) {l : List (ℕ × ℕ)}
    (hc : ¬ Consistent l) (s : Option Sentence) : tierAPrice sk c n t (l, s) = 0 := by
  simp only [tierAPrice]; rw [if_neg hc]

/-- `tierAPrice` is in `[0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tierAPrice_mem_Icc {n : ℕ} (t : Table smallIndex n) (s : List (ℕ × ℕ) × Option Sentence) :
    0 ≤ tierAPrice sk c n t s ∧ tierAPrice sk c n t s ≤ 1 := by
  obtain ⟨l, s⟩ := s
  by_cases hc : Consistent l
  · rw [tierAPrice_of_consistent c sk t hc]
    have h1 := chainMass_mem_Icc c sk n t l
    have h2 := smallFactor_mem_Icc c l s
    exact ⟨mul_nonneg h1.1 h2.1, mul_le_one₀ h1.2 h2.1 h2.2⟩
  · rw [tierAPrice_of_not_consistent c sk t hc]; exact ⟨le_rfl, zero_le_one⟩

variable {c} {sk} {Q : RatHistory}

/-- `bliPrice` on a small sentence is the base's price.
Source: [[bli-program]] §2.5 (constraint 1)
Kind: L
Fidelity: n/a -/
lemma bliPrice_of_small {n : ℕ} {ψ : Sentence} (h : SmallOn n ψ) :
    bliPrice Q 𝓜 sk c n ψ = Q n ψ := by
  unfold bliPrice; rw [if_pos h]

/-- `bliPrice` on a large Tier-A sentence is its Tier-A price from the unrounded actual table.
Source: [[bli-program]] §2.5
Kind: L
Fidelity: n/a -/
lemma bliPrice_of_tierA {n : ℕ} {ψ : Sentence} (h : ¬ SmallOn n ψ)
    {s : List (ℕ × ℕ) × Option Sentence} (ht : tierA c n ψ = some s) :
    bliPrice Q 𝓜 sk c n ψ = tierAPrice sk c n (actualTable smallIndex Q n) s := by
  unfold bliPrice; rw [if_neg h]; simp only [ht]

/-- `bliPrice` on a large Tier-B sentence is the base's price.
Source: [[bli-program]] §2.5 (Tier B)
Kind: L
Fidelity: n/a -/
lemma bliPrice_of_tierB {n : ℕ} {ψ : Sentence} (h : ¬ SmallOn n ψ) (ht : tierA c n ψ = none) :
    bliPrice Q 𝓜 sk c n ψ = Q n ψ := by
  unfold bliPrice; rw [if_neg h]; simp only [ht]

/-- `b0Price` on a small sentence is the base's price.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma b0Price_of_small {n : ℕ} {ψ : Sentence} (h : SmallOn n ψ) :
    b0Price Q 𝓜 c n ψ = Q n ψ := by
  unfold b0Price; rw [if_pos h]

/-- `b0Price` on a large Tier-A sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma b0Price_of_tierA {n : ℕ} {ψ : Sentence} (h : ¬ SmallOn n ψ)
    {l : List (ℕ × ℕ)} {s : Option Sentence} (ht : tierA c n ψ = some (l, s)) :
    b0Price Q 𝓜 c n ψ =
      if ∀ x ∈ l, x.2 = c.code x.1 (degAt 𝓜.d (actualTable smallIndex Q n) x.1)
      then smallFactor c l s else 0 := by
  unfold b0Price; rw [if_neg h]; simp only [ht]

/-- `b0Price` on a large Tier-B sentence is the base's price.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma b0Price_of_tierB {n : ℕ} {ψ : Sentence} (h : ¬ SmallOn n ψ) (ht : tierA c n ψ = none) :
    b0Price Q 𝓜 c n ψ = Q n ψ := by
  unfold b0Price; rw [if_neg h]; simp only [ht]

/-! ## Additivity over a day's codes (M3, `bli_stateAlgebra_additive`) -/

/-- **`chainProbH_sum_states` — additivity over a day's codes**: for `n < m ≤ n + H`, summing the
chain probability with an extra day-`m` entry `(m, q)` over the day-`m` candidates `q` gives the
chain probability without it — the marginal over day `m` is the sum over its codes, i.e. the
Tier-A prices are the marginals of one probability. The horizon condition `m ≤ n + H` is
necessary: beyond the horizon the entry is inert and the sum is `card (states m)` times the value
(report §M3). Proof: at `m = n+1` the entry selects the code of the day-`(n+1)` table, which is a
candidate (`code_mem_states`), so the inner sum collapses (`Finset.sum_ite_eq`); at `m > n+1` the
entry is inert on the first step and the identity recurses from day `n+1`.
Source: [[bli-program]] §3.5 (i); mandate M3 (`bli_stateAlgebra_additive`)
Kind: P
Fidelity: exact (the additivity identity, with the horizon condition stated)
Hyps: (a) `n < m ≤ n + H` -/
theorem chainProbH_sum_states (l : List (ℕ × ℕ)) :
    ∀ (H n : ℕ) (t : Table smallIndex n) (m : ℕ), n < m → m ≤ n + H →
      ∑ q ∈ c.states m, chainProbH sk c ((m, q) :: l) n t H = chainProbH sk c l n t H
  | 0, _, _, _, hnm, hmH => by omega
  | H + 1, n, t, m, hnm, hmH => by
    simp only [chainProbH_succ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun Q hQ => ?_
    rw [← Finset.mul_sum]
    congr 1
    by_cases hm : m = n + 1
    · subst hm
      have hcons : ∀ q, chainProbH sk c ((n + 1, q) :: l) (n + 1) Q H =
          chainProbH sk c l (n + 1) Q H :=
        fun q => chainProbH_cons_of_le c sk l H (n + 1) Q le_rfl
      have hcond : ∀ q, (∀ x ∈ (n + 1, q) :: l, x.1 = n + 1 → c.code (n + 1) Q = x.2) ↔
          (c.code (n + 1) Q = q ∧ ∀ x ∈ l, x.1 = n + 1 → c.code (n + 1) Q = x.2) := by
        intro q; simp
      simp only [hcons, hcond]
      by_cases hR : ∀ x ∈ l, x.1 = n + 1 → c.code (n + 1) Q = x.2
      · simp only [eq_true hR, and_true, if_true]
        rw [Finset.sum_ite_eq]
        rw [if_pos (c.code_mem_states hQ)]
      · simp only [eq_false hR, and_false, if_false, Finset.sum_const_zero]
    · have hcond : ∀ q, (∀ x ∈ (m, q) :: l, x.1 = n + 1 → c.code (n + 1) Q = x.2) ↔
          (∀ x ∈ l, x.1 = n + 1 → c.code (n + 1) Q = x.2) := by
        intro q
        simp only [List.forall_mem_cons]
        exact ⟨fun h => h.2, fun h => ⟨fun h1 => absurd h1 hm, h⟩⟩
      simp only [hcond]
      by_cases hR : ∀ x ∈ l, x.1 = n + 1 → c.code (n + 1) Q = x.2
      · simp only [eq_true hR, if_true]
        exact chainProbH_sum_states l H (n + 1) Q m (by omega) (by omega)
      · simp only [eq_false hR, if_false, Finset.sum_const_zero]

end Cleanroom.Bli.BliTrajectory
