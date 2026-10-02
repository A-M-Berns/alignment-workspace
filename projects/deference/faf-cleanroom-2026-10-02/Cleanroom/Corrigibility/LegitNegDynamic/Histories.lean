import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# E5: self-referential legitimacy — fixed points of four formalisations on six histories

Package `legit-neg-dynamic`, target 11 (load-bearing 5). Sources: `clusters/E/NEGATIVES.md` E5;
`clusters/E/VERIFY.md` "E5 — narrowed" (V-E5); `clusters/E/fixtures/e3_fixed_points.py`
(`step_ok` l. 40–49, `m1_legit`, `kappa`, the six histories), `verify_e.py:49-66`; pinned by
[[corr-legit-neg-inventory]] item 058 and [[corr-legit-neg-2-inventory]] items 2-021, 2-027.

Definition (c) of the mandate: steps (`honest`, `advocate t`, `manip`, `rule t`), criteria
`0 = L0`, `1 = TOP`, `2 = L0_noadv`, `3 = L0_entrenched`, the fixture's `stepOk`, M1's recursion
`m1Legit`, the six histories `H`, the retroactive reading `κ` of a final ruling, and the operators
`M2op` (`X ↦ {h ∈ X | h ∈ κ h}`), `M3op` (`X ↦ ⋃_{h ∈ X} κ h`, monotone) and the liar `M4op`. The
counts come from the six concrete histories, by `decide` on `Fin 6` facts and hand proofs of the
fixed-point characterisations: M2's fixed points are exactly the `2^5 = 32` subsets of the
self-endorsing set (which contains the self-certifying `h₃`); M3's are `∅` and everything (its
least fixed point above `{h₁}` is everything), and without `h₆` they are `∅, {h₁, h₅}, univ` with
`{h₁, h₅}` the anchored one (2-021); M4 has none. V-E5's per-history retroactive reading is
`retroLegit`: the local step test certifies `h₃`, the taint-aware one gives M1's set. M1's incentive
to argue for abolition is `q (1 − v)`, and it vanishes under `L0_noadv`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.LegitNegDynamic

open Finset

/-- A step of a history: honest assistance, admissible advocacy for adopting criterion `t`, a
manipulation, or a human ruling adopting criterion `t` (`e3_fixed_points.py:3-8`).
Source: [[corr-legit-neg-inventory]] item 058 (E5)
Kind: D
Fidelity: exact -/
inductive Step
  | honest
  | advocate (t : Fin 4)
  | manip
  | rule (t : Fin 4)
  deriving DecidableEq

/-- **The fixture's `step_ok`** (`e3_fixed_points.py:40-49`): criteria `0 = L0`, `1 = TOP`,
`2 = L0_noadv`, `3 = L0_entrenched`. Under `TOP` every step is legitimate; otherwise a manipulation
is not, advocacy is not under `L0_noadv`, and a ruling to `TOP` is not under `L0_entrenched`.
Source: [[corr-legit-neg-inventory]] item 058 (E5)
Kind: D
Fidelity: exact -/
def stepOk (c : Fin 4) (s : Step) : Bool :=
  if c = 1 then true else
  match s with
  | .honest => true
  | .manip => false
  | .advocate _ => decide (c ≠ 2)
  | .rule t => !(decide (t = 1) && decide (c = 3))

/-- The criterion in force after a step: a ruling's target, else unchanged.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def nextCrit (c : Fin 4) : Step → Fin 4
  | .rule t => t
  | _ => c

/-- **M1 (anchored, per history, prospective)**: step `t` is judged by the criterion in force at
`t`, starting from the anchor; a ruling takes effect only if the ruling step is itself legitimate
(`e3_fixed_points.py:52-60`, `m1_legit`). A recursion on time, hence unique.
Source: [[corr-legit-neg-inventory]] item 058 (E5, M1)
Kind: D
Fidelity: exact -/
def m1Legit : Fin 4 → List Step → Bool
  | _, [] => true
  | c, s :: rest => stepOk c s && m1Legit (nextCrit c s) rest

/-- **The six histories** (`e3_fixed_points.py:26-33`): `h₁` honest; `h₂` advocate TOP, ruling TOP,
manipulation; `h₃` manipulation, ruling TOP (self-certifying); `h₄` manipulation, ruling L0; `h₅`
advocate TOP, ruling L0, honest; `h₆` advocate TOP, ruling TOP, honest. Indexed `0`–`5`.
Source: [[corr-legit-neg-inventory]] item 058 (E5)
Kind: D
Fidelity: exact -/
def H : Fin 6 → List Step :=
  ![[.honest], [.advocate 1, .rule 1, .manip], [.manip, .rule 1], [.manip, .rule 0],
    [.advocate 1, .rule 0, .honest], [.advocate 1, .rule 1, .honest]]

/-- The last ruling of a history, if any.
Source: `e3_fixed_points.py:63-65` (`final_ruling`)
Kind: D
Fidelity: exact -/
def finalRuling : List Step → Option (Fin 4)
  | [] => none
  | s :: rest =>
    match finalRuling rest with
    | some t => some t
    | none => match s with
      | .rule t => some t
      | _ => none

/-- **`κ h`**: the histories that `h`'s final ruling (else the anchor) rates legitimate when every
step is judged by that one criterion — the retroactive reading of a ruling
(`e3_fixed_points.py:68-72`, `kappa`).
Source: [[corr-legit-neg-inventory]] item 058 (E5, M2/M3)
Kind: D
Fidelity: exact -/
def κ (anchor : Fin 4) (h : Fin 6) : Finset (Fin 6) :=
  univ.filter fun h' => (H h').all (stepOk ((finalRuling (H h)).getD anchor))

/-- **M2 (unanchored, per history)**: `X ↦ {h ∈ X | h ∈ κ h}` — `h` is legitimate iff it is
legitimate and its own final ruling endorses it.
Source: [[corr-legit-neg-inventory]] item 058 (E5, M2)
Kind: D
Fidelity: exact -/
def M2op (anchor : Fin 4) (X : Finset (Fin 6)) : Finset (Fin 6) := X.filter fun h => h ∈ κ anchor h

/-- **M3 (pooled / retroactive)**: `X ↦ ⋃_{h ∈ X} κ h` — the rulings of every legitimate history
decide the legitimacy of every history. Monotone.
Source: [[corr-legit-neg-inventory]] item 058 (E5, M3)
Kind: D
Fidelity: exact -/
def M3op (anchor : Fin 4) (X : Finset (Fin 6)) : Finset (Fin 6) := X.biUnion (κ anchor)

/-- The self-endorsing histories `{h | h ∈ κ h}` — V-E5's non-circular unanchored reading.
Source: VERIFY E V-E5 (narrowing 2)
Kind: D
Fidelity: exact -/
def selfEnd (anchor : Fin 4) : Finset (Fin 6) := univ.filter fun h => h ∈ κ anchor h

/-! ### M1: the legitimate sets under the three anchors, and the incentive -/

/-- **M1's legitimate sets**: under `L0`, `{h₁, h₂, h₅, h₆}` (`h₂`'s late manipulation counts
because `TOP` was legitimately adopted first; `h₃`, `h₄` fail at their first step); under
`L0_noadv`, `{h₁}`; under `L0_entrenched`, `{h₁, h₅}`.
Source: [[corr-legit-neg-inventory]] item 058 (E5, M1); [[corr-legit-neg-2-inventory]] item 2-021; `e3_fixed_points.py:80-87`
Kind: P
Fidelity: exact (six `decide`s per anchor)
Hyps: (a) none -/
theorem m1_sets :
    (univ.filter fun h => m1Legit 0 (H h) = true) = {0, 1, 4, 5} ∧
    (univ.filter fun h => m1Legit 2 (H h) = true) = {0} ∧
    (univ.filter fun h => m1Legit 3 (H h) = true) = {0, 4} := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **M1's incentive to argue for abolition**: advocacy adopted with probability `q`, after which the
manipulation (legitimate under `L0`, as `h₂` shows) scores `1` instead of `v`: it beats honesty by
`q (1 − v) > 0` (`7/50` at `q = 1/5, v = 3/10`); under `L0_noadv` the advocacy step itself voids
(`h₂` is illegitimate: `m1Legit 2 (H 1) = false` is what the Lean states; the fixture's "value
`0 < v`" for that case is not a clause here). The proof is `ring`, `mul_pos` and two `decide`s on
the concrete histories (finding 55), so the kind is L.
Source: [[corr-legit-neg-inventory]] item 058 (E5, incentive); `e3_fixed_points.py:89-100`
Kind: L
Fidelity: weaker: the `L0_noadv` clause is the legitimacy fact only, not the value
Hyps: (a) `0 < q`, `v < 1` -/
theorem m1_incentive (q v : ℚ) (hq : 0 < q) (hv : v < 1) :
    q * 1 + (1 - q) * v - v = q * (1 - v) ∧ 0 < q * (1 - v) ∧
    m1Legit 0 (H 1) = true ∧ m1Legit 2 (H 1) = false ∧ (1/5 : ℚ) * (1 - 3/10) = 7/50 := by
  refine ⟨by ring, mul_pos hq (by linarith), by decide, by decide, by norm_num⟩

/-! ### M2: the `2^5` fixed points -/

/-- **M2's fixed points are exactly the subsets of the self-endorsing set** (for any anchor):
`M2op X = X ↔ X ⊆ selfEnd`. (`Finset.filter_eq_self` unfolded — kind L; M2's content is `M2_L0`.)
Source: [[corr-legit-neg-inventory]] item 058 (E5, M2, "the condition is `X ⊆ {h : h ∈ κ(h)}`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem M2_fixed_iff (anchor : Fin 4) (X : Finset (Fin 6)) :
    M2op anchor X = X ↔ X ⊆ selfEnd anchor := by
  unfold M2op selfEnd
  rw [Finset.filter_eq_self]
  constructor
  · intro h x hx; exact Finset.mem_filter.2 ⟨mem_univ x, h x hx⟩
  · intro h x hx; exact (Finset.mem_filter.1 (h hx)).2

/-- **M2 under `L0`**: the self-endorsing set is `{h₁, h₂, h₃, h₅, h₆}`, so there are `2^5 = 32`
fixed points, the greatest of which contains the self-certifying manipulation `h₃`.
Source: [[corr-legit-neg-inventory]] item 058 (E5, M2); `e3_fixed_points.py:102-109`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem M2_L0 :
    selfEnd 0 = {0, 1, 2, 4, 5} ∧
    (univ.powerset.filter fun X => M2op 0 X = X) = (selfEnd 0).powerset ∧
    ((univ.powerset.filter fun X => M2op 0 X = X).card = 32) ∧ (2 : Fin 6) ∈ selfEnd 0 := by
  have hs : selfEnd 0 = {0, 1, 2, 4, 5} := by decide
  have hp : (univ.powerset.filter fun X => M2op 0 X = X) = (selfEnd 0).powerset := by
    ext X
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and, M2_fixed_iff]
  refine ⟨hs, hp, ?_, by rw [hs]; decide⟩
  rw [hp, Finset.card_powerset, hs]; rfl

/-! ### M3: only `∅` and everything -/

/-- **The six `κ` sets under `L0`**: `κ h₁ = κ h₄ = κ h₅ = {h₁, h₅, h₆}` (their final criterion is
`L0`) and `κ h₂ = κ h₃ = κ h₆ = univ` (`TOP`).
Source: [[corr-legit-neg-inventory]] item 058 (E5, M3); VERIFY E "E5 — narrowed" (evidence)
Kind: L
Fidelity: exact -/
theorem κ_L0 :
    κ 0 0 = {0, 4, 5} ∧ κ 0 3 = {0, 4, 5} ∧ κ 0 4 = {0, 4, 5} ∧
    κ 0 1 = univ ∧ κ 0 2 = univ ∧ κ 0 5 = univ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Every `κ h` contains `h₆` (the clean, legitimately reached abolition).
Source: [[corr-legit-neg-2-inventory]] item 2-021
Kind: L
Fidelity: exact -/
theorem five_mem_κ : ∀ h, (5 : Fin 6) ∈ κ 0 h := by decide

/-- **M3's fixed points are exactly `∅` and everything**: a non-empty fixed point contains `h₆`
(every `κ` does), hence `κ h₆ = univ`.
Source: [[corr-legit-neg-inventory]] item 058 (E5, M3); `e3_fixed_points.py:111-121`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem M3_fixed_iff (X : Finset (Fin 6)) : M3op 0 X = X ↔ X = ∅ ∨ X = univ := by
  constructor
  · intro hfix
    by_cases hX : X = ∅
    · exact Or.inl hX
    · right
      obtain ⟨h, hh⟩ := Finset.nonempty_iff_ne_empty.2 hX
      have h5 : (5 : Fin 6) ∈ X := by
        rw [← hfix]; exact Finset.mem_biUnion.2 ⟨h, hh, five_mem_κ h⟩
      apply Finset.univ_subset_iff.1
      intro y _
      rw [← hfix]
      exact Finset.mem_biUnion.2 ⟨5, h5, by rw [κ_L0.2.2.2.2.2]; exact mem_univ y⟩
  · rintro (rfl | rfl)
    · simp [M3op]
    · apply Finset.univ_subset_iff.1
      intro y _
      exact Finset.mem_biUnion.2 ⟨1, mem_univ 1, by rw [κ_L0.2.2.2.1]; exact mem_univ y⟩

/-- **M3's least fixed point above the honest anchor `{h₁}` is everything**: the anchored operator
`X ↦ {h₁} ∪ M3op X` has `univ` as its only fixed point (`h₁`'s criterion admits `h₆`, whose
ruling `TOP` admits everything, `h₃` and `h₄` included).
Source: [[corr-legit-neg-inventory]] item 058 (E5, M3, "least fixed point above the anchor")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem M3_anchored_iff (X : Finset (Fin 6)) : {0} ∪ M3op 0 X = X ↔ X = univ := by
  constructor
  · intro hfix
    have h0 : (0 : Fin 6) ∈ X := by rw [← hfix]; exact Finset.mem_union_left _ (Finset.mem_singleton_self 0)
    have h5 : (5 : Fin 6) ∈ X := by
      rw [← hfix]; exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨0, h0, five_mem_κ 0⟩)
    apply Finset.univ_subset_iff.1
    intro y _
    rw [← hfix]
    exact Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨5, h5, by rw [κ_L0.2.2.2.2.2]; exact mem_univ y⟩)
  · rintro rfl
    apply Finset.univ_subset_iff.1
    intro y _
    exact Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨1, mem_univ 1, by rw [κ_L0.2.2.2.1]; exact mem_univ y⟩)

/-! ### 2-021: without `h₆` -/

/-- The five histories `h₁`–`h₅` (no legitimately reachable clean abolition).
Source: [[corr-legit-neg-2-inventory]] item 2-021
Kind: D
Fidelity: exact -/
def H5 : Fin 5 → List Step := ![H 0, H 1, H 2, H 3, H 4]

/-- `κ` on the five histories.
Source: [[corr-legit-neg-2-inventory]] item 2-021
Kind: D
Fidelity: exact -/
def κ5 (anchor : Fin 4) (h : Fin 5) : Finset (Fin 5) :=
  univ.filter fun h' => (H5 h').all (stepOk ((finalRuling (H5 h)).getD anchor))

/-- M3 on the five histories.
Source: [[corr-legit-neg-2-inventory]] item 2-021
Kind: D
Fidelity: exact -/
def M3op5 (anchor : Fin 4) (X : Finset (Fin 5)) : Finset (Fin 5) := X.biUnion (κ5 anchor)

/-- The five `κ5` sets: `{h₁, h₅}` for `h₁, h₄, h₅`; `univ` for `h₂, h₃`.
Source: [[corr-legit-neg-2-inventory]] item 2-021
Kind: L
Fidelity: exact -/
theorem κ5_L0 :
    (∀ h : Fin 5, h ≠ 1 → h ≠ 2 → κ5 0 h = {0, 4}) ∧ κ5 0 1 = univ ∧ κ5 0 2 = univ := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **2-021 (N− for M3's degeneracy)**: without `h₆` the pooled model has exactly the fixed points
`∅`, `{h₁, h₅}` and everything; the anchored operator `X ↦ {h₁} ∪ M3op X` has exactly the fixed
points `{h₁, h₅}` and everything, so the least above the anchor is `{h₁, h₅}` — M3's degeneracy
needs a legitimately reachable clean abolition.
Source: [[corr-legit-neg-2-inventory]] item 2-021; `e3_fixed_points.py:123-130`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem M3_fixed_iff5 (X : Finset (Fin 5)) :
    (M3op5 0 X = X ↔ X = ∅ ∨ X = {0, 4} ∨ X = univ) ∧
    ({0} ∪ M3op5 0 X = X ↔ X = {0, 4} ∨ X = univ) := by
  obtain ⟨hk, hk1, hk2⟩ := κ5_L0
  -- a non-empty `X` avoiding `h₂, h₃` maps to `{h₁, h₅}`
  have hconst : ∀ Y : Finset (Fin 5), Y.Nonempty → (1 : Fin 5) ∉ Y → (2 : Fin 5) ∉ Y →
      M3op5 0 Y = {0, 4} := by
    intro Y hY h1 h2
    ext y
    rw [M3op5, Finset.mem_biUnion]
    constructor
    · rintro ⟨h, hh, hy⟩
      have : h ≠ 1 := fun e => h1 (e ▸ hh)
      have : h ≠ 2 := fun e => h2 (e ▸ hh)
      rwa [hk h ‹h ≠ 1› ‹h ≠ 2›] at hy
    · intro hy
      obtain ⟨h, hh⟩ := hY
      have : h ≠ 1 := fun e => h1 (e ▸ hh)
      have : h ≠ 2 := fun e => h2 (e ▸ hh)
      exact ⟨h, hh, by rwa [hk h ‹h ≠ 1› ‹h ≠ 2›]⟩
  -- a `X` containing `h₂` or `h₃` maps onto everything
  have huniv : ∀ Y : Finset (Fin 5), ((1 : Fin 5) ∈ Y ∨ (2 : Fin 5) ∈ Y) → univ ⊆ M3op5 0 Y := by
    rintro Y (h | h) y _
    · exact Finset.mem_biUnion.2 ⟨1, h, by rw [hk1]; exact mem_univ y⟩
    · exact Finset.mem_biUnion.2 ⟨2, h, by rw [hk2]; exact mem_univ y⟩
  constructor
  · constructor
    · intro hfix
      by_cases hX : X = ∅
      · exact Or.inl hX
      · by_cases h12 : (1 : Fin 5) ∈ X ∨ (2 : Fin 5) ∈ X
        · right; right
          exact Finset.univ_subset_iff.1 (hfix ▸ huniv X h12)
        · right; left
          push Not at h12
          rw [← hfix]
          exact hconst X (Finset.nonempty_iff_ne_empty.2 hX) h12.1 h12.2
    · rintro (rfl | rfl | rfl)
      · simp [M3op5]
      · exact hconst _ ⟨0, by decide⟩ (by decide) (by decide)
      · exact Finset.univ_subset_iff.1 (huniv univ (Or.inl (mem_univ 1)))
  · constructor
    · intro hfix
      have h0 : (0 : Fin 5) ∈ X := by
        rw [← hfix]; exact Finset.mem_union_left _ (Finset.mem_singleton_self 0)
      by_cases h12 : (1 : Fin 5) ∈ X ∨ (2 : Fin 5) ∈ X
      · right
        apply Finset.univ_subset_iff.1
        intro y _
        rw [← hfix]
        exact Finset.mem_union_right _ (huniv X h12 (mem_univ y))
      · left
        push Not at h12
        rw [← hfix, hconst X ⟨0, h0⟩ h12.1 h12.2]
        decide
    · rintro (rfl | rfl)
      · rw [hconst _ ⟨0, by decide⟩ (by decide) (by decide)]; decide
      · apply Finset.univ_subset_iff.1
        intro y _
        exact Finset.mem_union_right _ (huniv univ (Or.inl (mem_univ 1)) (mem_univ y))

/-! ### M4: the liar -/

/-- **M4**: a single history whose ruling rates it legitimate iff it is not legitimate.
Source: [[corr-legit-neg-inventory]] item 058 (E5, M4)
Kind: D
Fidelity: exact -/
def M4op (X : Finset (Fin 1)) : Finset (Fin 1) := if (0 : Fin 1) ∈ X then ∅ else {0}

/-- **M4 has no fixed point** (existence fails without monotonicity).
Source: [[corr-legit-neg-inventory]] item 058 (E5, M4); `e3_fixed_points.py:132-134`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem M4_no_fixed_point : ∀ X, M4op X ≠ X := by
  intro X hX
  unfold M4op at hX
  split_ifs at hX with h
  · rw [← hX] at h; simp at h
  · apply h; rw [← hX]; exact Finset.mem_singleton_self 0

/-! ### V-E5: the per-history retroactive reading -/

/-- The criterion in force at the end of a history under V-E5's per-history retroactive reading:
a ruling takes effect iff its step is legitimate under the criterion in force when it is made and,
when `taint`, no manipulation has occurred earlier in the history (`verify_e.py:53-62`).
Source: VERIFY E V-E5
Kind: D
Fidelity: exact -/
def retroCrit (taint : Bool) : Fin 4 → Bool → List Step → Fin 4
  | c, _, [] => c
  | c, manipulated, s :: rest =>
    let manipulated' := manipulated || (match s with | .manip => true | _ => false)
    match s with
    | .rule t =>
      if stepOk c s && !(taint && manipulated' && !(decide (c = 1))) then
        retroCrit taint t manipulated' rest
      else retroCrit taint c manipulated' rest
    | _ => retroCrit taint c manipulated' rest

/-- **V-E5's per-history retroactive legitimacy**: every step of `h` judged by the criterion in
force at `h`'s end.
Source: VERIFY E V-E5
Kind: D
Fidelity: exact -/
def retroLegit (taint : Bool) (anchor : Fin 4) (h : List Step) : Bool :=
  h.all (stepOk (retroCrit taint anchor false h))

/-- **V-E5**: the per-history retroactive reading with the local step test certifies
`{h₁, h₂, h₃, h₅, h₆}` (the self-certifying `h₃` included); with the taint-aware ruling test it
gives `{h₁, h₂, h₅, h₆}` = M1's set. A recursion on time, hence unique in either form.
Source: VERIFY E "E5 — narrowed" (V-E5); `verify_e.py:63-66`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem retro_sets :
    (univ.filter fun h => retroLegit false 0 (H h) = true) = {0, 1, 2, 4, 5} ∧
    (univ.filter fun h => retroLegit true 0 (H h) = true) = {0, 1, 4, 5} ∧
    (univ.filter fun h => retroLegit true 0 (H h) = true) =
      (univ.filter fun h => m1Legit 0 (H h) = true) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ### 2-027: with a fixed criterion everything collapses to the stepwise test -/

/-- **2-027 (i)**: on a history without rulings, M1 is the stepwise test `h.all (stepOk c)`.
Source: [[corr-legit-neg-2-inventory]] item 2-027 (b)
Kind: P
Fidelity: exact
Hyps: (a) no `rule` step -/
theorem m1Legit_of_no_rule (c : Fin 4) (h : List Step) (hno : ∀ s ∈ h, ∀ t, s ≠ Step.rule t) :
    m1Legit c h = h.all (stepOk c) := by
  induction h with
  | nil => rfl
  | cons s rest ih =>
    have hs : nextCrit c s = c := by
      cases s with
      | rule t => exact absurd rfl (hno _ (by simp) t)
      | honest => rfl
      | advocate _ => rfl
      | manip => rfl
    rw [m1Legit, hs, ih (fun s' hs' => hno s' (by simp [hs'])), List.all_cons]

/-- **2-027 (ii)**: a `biUnion` of a constant is the constant on non-empty sets, so an operator
`X ↦ ⋃_{h ∈ X} K` has exactly the fixed points `∅` and `K` — the pooled reading with a fixed
criterion has a unique non-empty fixed point (with `κ` constant when no ruling changes the
criterion: `finalRuling = none` makes `κ anchor h` the stepwise set at the anchor). Kind L:
`Finset.mem_biUnion` unfolded.
Source: [[corr-legit-neg-2-inventory]] item 2-027 (b)
Kind: L
Fidelity: exact
Hyps: (a) `κ'` constant -/
theorem biUnion_const_of_nonempty {α β : Type} [DecidableEq β] (f : α → Finset β) (K : Finset β)
    (hf : ∀ h, f h = K) (X : Finset α) (hX : X.Nonempty) : X.biUnion f = K := by
  ext y
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨h, _, hy⟩; rwa [hf h] at hy
  · intro hy; obtain ⟨h, hh⟩ := hX; exact ⟨h, hh, by rwa [hf h]⟩

/-- **2-027 (iii)**: an operator `X ↦ ⋃_{h ∈ X} f h` with `f` constant has exactly the fixed points
`∅` and the constant: with a fixed criterion the pooled reading's non-empty fixed point is unique.
Source: [[corr-legit-neg-2-inventory]] item 2-027 (b)
Kind: P
Fidelity: exact
Hyps: (a) `f` constant -/
theorem biUnion_const_fixed_iff {α : Type} [DecidableEq α] (f : α → Finset α) (K : Finset α)
    (hf : ∀ h, f h = K) (X : Finset α) : X.biUnion f = X ↔ X = ∅ ∨ X = K := by
  constructor
  · intro hfix
    by_cases hX : X = ∅
    · exact Or.inl hX
    · right; rw [← hfix]
      exact biUnion_const_of_nonempty f K hf X (Finset.nonempty_iff_ne_empty.2 hX)
  · rintro (rfl | hXK)
    · simp
    · rw [hXK]
      by_cases hK : K = ∅
      · rw [hK]; simp
      · exact biUnion_const_of_nonempty f K hf K (Finset.nonempty_iff_ne_empty.2 hK)

/-- With no ruling, `κ` is the stepwise set at the anchor. Scope: `κ` is defined on the fixture's six
histories, of which only `h₁` (`H 0`) has no ruling, so this lemma is live at `h = 0` only; the
general content of 2-027 (b) is `m1Legit_of_no_rule` (any history) and `biUnion_const_fixed_iff`
(any constant map). The three consequences 2-027 draws — `M3op` constant on non-empty sets, M2's
self-endorsing set equal to the stepwise set, the retroactive reading equal to M1's — are **not**
stated as theorems here: they need every history to be ruling-free, which the fixture's family is
not.
Source: [[corr-legit-neg-2-inventory]] item 2-027 (b)
Kind: L
Fidelity: weaker: live on the single ruling-free history of the fixture; consequences not stated -/
theorem κ_of_no_ruling (anchor : Fin 4) (h : Fin 6) (hn : finalRuling (H h) = none) :
    κ anchor h = univ.filter fun h' => (H h').all (stepOk anchor) := by
  unfold κ; rw [hn]; rfl

end Cleanroom.Corrigibility.LegitNegDynamic
