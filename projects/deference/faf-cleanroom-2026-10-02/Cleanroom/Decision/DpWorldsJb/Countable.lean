import Cleanroom.Decision.DpWorldsJb.Annihilation
import Cleanroom.Decision.DpWorldsJb.Worlds
import Cleanroom.Decision.DpWorldsJb.Dyadic
import Mathlib.Order.Atoms
import Mathlib.Data.Countable.Defs

/-!
# Worlds of countable algebras under `Jω` (T6, sharpened; audit r1 N2 agenda item)

On a **countable** Boolean algebra every `Jω`-world holds an atom — by a diagonal argument
that uses no measure: enumerate `E = {e₀, e₁, …}`; for each non-`⊥` `eₙ` pick a member `Yₙ`
of the world with `eₙ ≰ Yₙ` (`eₙᶜ` if `eₙ ∉ ω`; a proper non-`⊥` part of `eₙ` or its
complement in `eₙ` if `eₙ ∈ ω` is not an atom); `{Yₙ}` is a countable family of members whose
only lower bound is `⊥`, so it is `Jω`-designated with infimum `⊥`, and constraint 4 puts `⊥`
in the world. Consequences:

* `worldJω_equiv_atoms`: on a countable algebra the `Jω`-worlds are exactly the atoms, through
  the **atom world** `atomWorld J b := {X | b ≤ X}` — a world for *every* designation on *any*
  Boolean algebra (the general form of `principalWorld`, `principalWorld_eq_atomWorld`);
* `no_world_of_countable_atomless`: a countable atomless algebra has no `Jω`-worlds, with no
  measure, no strict positivity and no halving;
* `Dy.countable` and `dyadic_no_world_of_countable`: the package's N+ witness for
  `no_world_of_halving` is countable, so its conclusion also follows from atomlessness alone.
  The halving hypothesis of `no_world_of_halving` earns its keep only on **uncountable**
  algebras — the appendix's own instance, the Lebesgue measure algebra, which is not built
  here (an uncountable N+ witness for the halving theorem is an open agenda item).
-/

namespace Cleanroom.Decision.DpWorldsJb

noncomputable section

open Classical

variable {E : Type*} [BooleanAlgebra E]

/-! ### Atom worlds -/

/-- The **atom world** `{X | b ≤ X}` at an atom `b`: a world for **every** designation `J` on
any Boolean algebra, because an atom below every member of a family is below its infimum.
Generalizes `principalWorld` (`principalWorld_eq_atomWorld`).
Source: [[decision-problems-v2]] Appendix A "Typing the designation" (principal ultrafilters = points) | dp-core-2-057
Kind: D
Fidelity: exact
Hyps: n/a -/
def atomWorld (J : Designation E) (b : E) (hb : IsAtom b) : World J where
  carrier := {X | b ≤ X}
  exactly_one := fun X => by
    show b ≤ X ↔ ¬ b ≤ Xᶜ
    constructor
    · intro h h'
      have hle : b ≤ X ⊓ Xᶜ := le_inf h h'
      rw [inf_compl_eq_bot] at hle
      exact hb.1 (le_bot_iff.1 hle)
    · intro h
      rcases hb.le_iff.1 (inf_le_left : b ⊓ X ≤ b) with h0 | h1
      · exfalso
        apply h
        rw [le_compl_iff_disjoint_right, disjoint_iff]
        exact h0
      · calc b = b ⊓ X := h1.symm
          _ ≤ X := inf_le_right
  upward := fun _ _ h hle => le_trans h hle
  meet := fun _ _ h₁ h₂ => le_inf h₁ h₂
  designated := fun _ _ hall _ hm => hm.2 (fun A hA => hall A hA)

theorem mem_atomWorld (J : Designation E) (b : E) (hb : IsAtom b) (X : E) :
    X ∈ atomWorld J b hb ↔ b ≤ X := Iff.rfl

/-- A world containing an atom `b` is the atom world at `b`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem World.eq_atomWorld_of_mem {J : Designation E} (ω : World J) {b : E} (hb : IsAtom b)
    (h : b ∈ ω) : ω = atomWorld J b hb := by
  ext X
  constructor
  · intro hX
    have hm : b ⊓ X ∈ ω := ω.meet _ _ h hX
    have hne : b ⊓ X ≠ ⊥ := fun e => ω.bot_notMem (e ▸ hm)
    rcases hb.le_iff.1 (inf_le_left : b ⊓ X ≤ b) with h0 | h1
    · exact absurd h0 hne
    · show b ≤ X
      calc b = b ⊓ X := h1.symm
        _ ≤ X := inf_le_right
  · intro hX
    exact ω.upward b X h hX

/-- On a power set the point world is the atom world at the singleton.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem principalWorld_eq_atomWorld {α : Type*} (J : Designation (Set α)) (x : α) :
    principalWorld J x = atomWorld J {x} (Set.isAtom_singleton x) := by
  ext s
  show x ∈ s ↔ ({x} : Set α) ⊆ s
  exact Set.singleton_subset_iff.symm

/-! ### The diagonal argument on countable algebras -/

/-- If a world does not hold `b`, or holds `b` but `b` is not an atom, some member of the world
is not above `b`.
Source: none: infrastructure (audit r1 probes)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem World.exists_mem_not_le {J : Designation E} (ω : World J) (b : E) (hb : b ≠ ⊥)
    (hsplit : b ∈ ω → ∃ Z, Z < b ∧ Z ≠ ⊥) : ∃ Y ∈ ω, ¬ b ≤ Y := by
  by_cases hbω : b ∈ ω
  · obtain ⟨Z, hZlt, hZne⟩ := hsplit hbω
    have hZb : Z ⊔ (b \ Z) = b := sup_sdiff_cancel_right hZlt.le
    have hmem : Z ⊔ (b \ Z) ∈ ω := by rw [hZb]; exact hbω
    rcases ω.mem_or_mem_of_sup_mem hmem with hZ | hZ'
    · exact ⟨Z, hZ, fun hle => absurd (lt_of_le_of_lt hle hZlt) (lt_irrefl _)⟩
    · refine ⟨b \ Z, hZ', fun hle => ?_⟩
      have hlt : b \ Z < b := sdiff_lt hZlt.le hZne
      exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl _)
  · refine ⟨bᶜ, (ω.compl_mem_iff b).2 hbω, fun hle => hb ?_⟩
    have hle' : b ≤ b ⊓ bᶜ := le_inf le_rfl hle
    rw [inf_compl_eq_bot] at hle'
    exact le_bot_iff.1 hle'

/-- **On a countable Boolean algebra every `Jω`-world holds an atom** — the diagonal argument,
no measure involved.
Source: [[decision-problems-v2]] Appendix A "Annihilation", sharpened (audit r1 N2) | dp-core-2-058
Kind: P
Fidelity: stronger: no measure, no strict positivity, no halving; countability in their place
Hyps: (a) -/
theorem exists_atom_mem_of_countable [Countable E] (ω : World (Jω E)) : ∃ b ∈ ω, IsAtom b := by
  by_contra hno
  push Not at hno
  haveI : Nonempty E := ⟨⊤⟩
  obtain ⟨e, he⟩ := exists_surjective_nat E
  have step : ∀ n : ℕ, ∃ Y, Y ∈ ω ∧ (e n ≠ ⊥ → ¬ e n ≤ Y) := by
    intro n
    by_cases hn : e n = ⊥
    · exact ⟨⊤, ω.top_mem, fun h => absurd hn h⟩
    · have hsplit : e n ∈ ω → ∃ Z, Z < e n ∧ Z ≠ ⊥ := by
        intro hmem
        have hna : ¬ IsAtom (e n) := hno (e n) hmem
        unfold IsAtom at hna
        push Not at hna
        obtain ⟨Z, hZ, hZne⟩ := hna hn
        exact ⟨Z, hZ, hZne⟩
      obtain ⟨Y, hY, hle⟩ := ω.exists_mem_not_le (e n) hn hsplit
      exact ⟨Y, hY, fun _ => hle⟩
  choose Y hY using step
  have hglb : IsGLB (Set.range Y) ⊥ := by
    constructor
    · rintro _ ⟨n, rfl⟩
      exact bot_le
    · intro b hb
      by_contra hcon
      have hbne : b ≠ ⊥ := fun h => hcon (le_of_eq h)
      obtain ⟨n, rfl⟩ := he b
      exact (hY n).2 hbne (hb ⟨n, rfl⟩)
  have hD : Set.range Y ∈ (Jω E).1 := ⟨Set.countable_range _, ⊥, hglb⟩
  exact ω.bot_notMem (ω.designated _ hD (by rintro _ ⟨n, rfl⟩; exact (hY n).1) ⊥ hglb)

/-- **On a countable Boolean algebra the `Jω`-worlds are exactly the atoms**: `ω ↦` the atom it
holds, `b ↦ atomWorld (Jω E) b`. The general form of `worldJ₁_equiv_nat`.
Source: [[decision-problems-v2]] Appendix A "Annihilation" and "Typing the designation", sharpened (audit r1 N2) | dp-core-2-058
Kind: P
Fidelity: stronger: countable algebras in place of the appendix's measure-algebra setting
Hyps: (a) -/
def worldJω_equiv_atoms [Countable E] : World (Jω E) ≃ {b : E // IsAtom b} where
  toFun ω := ⟨Classical.choose (exists_atom_mem_of_countable ω),
    (Classical.choose_spec (exists_atom_mem_of_countable ω)).2⟩
  invFun b := atomWorld (Jω E) b.1 b.2
  left_inv ω := (ω.eq_atomWorld_of_mem _
    (Classical.choose_spec (exists_atom_mem_of_countable ω)).1).symm
  right_inv b := by
    apply Subtype.ext
    have hmem := (Classical.choose_spec (exists_atom_mem_of_countable (atomWorld (Jω E) b.1 b.2))).1
    have hat := (Classical.choose_spec (exists_atom_mem_of_countable (atomWorld (Jω E) b.1 b.2))).2
    have hle : b.1 ≤ Classical.choose (exists_atom_mem_of_countable (atomWorld (Jω E) b.1 b.2)) :=
      hmem
    exact ((hat.le_iff_eq b.2.1).1 hle).symm

/-- **A countable atomless Boolean algebra has no `Jω`-worlds** — annihilation with no measure,
no strict positivity and no halving.
Source: [[decision-problems-v2]] Appendix A "Annihilation", sharpened (audit r1 N2) | dp-core-2-058
Kind: C
Fidelity: stronger: countability and atomlessness in place of a strictly positive halving probability
Hyps: (a) -/
theorem no_world_of_countable_atomless [Countable E]
    (hat : ∀ X : E, X ≠ ⊥ → ∃ Y, Y < X ∧ Y ≠ ⊥) : IsEmpty (World (Jω E)) := by
  refine ⟨fun ω => ?_⟩
  obtain ⟨b, hb, hatom⟩ := exists_atom_mem_of_countable ω
  obtain ⟨Y, hYlt, hYne⟩ := hat b hatom.1
  exact hYne (hatom.2 Y hYlt)

/-! ### The dyadic witness is countable -/

/-- The dyadic algebra is countable: `(n, T) ↦ dySet n (T ∩ range (2 ^ n))` is onto.
Source: [[decision-problems-v2]] Appendix A "Annihilation" (the witness's cardinality; audit r1 N4/N2) | dp-core-2-058
Kind: L
Fidelity: exact
Hyps: n/a -/
instance Dy.countable : Countable Dy := by
  let f : ℕ × Finset ℕ → Dy := fun p =>
    ⟨dySet p.1 (p.2 ∩ Finset.range (2 ^ p.1)),
      ⟨p.1, p.2 ∩ Finset.range (2 ^ p.1), Finset.inter_subset_right, rfl⟩⟩
  apply Function.Surjective.countable (f := f)
  rintro ⟨s, hs⟩
  obtain ⟨n, T, hT, hsT⟩ := hs
  refine ⟨(n, T), ?_⟩
  apply Subtype.ext
  show dySet n (T ∩ Finset.range (2 ^ n)) = s
  rw [Finset.inter_eq_left.2 hT, hsT]

/-- `dyadic_no_world` re-derived from countability and atomlessness alone: the halving measure
is not needed on this witness (audit r1 N2). So `Dy` inhabits the hypotheses of
`no_world_of_halving` (N+ for the theorem as stated) but does not separate it from its
measure-free countable special case.
Source: [[decision-problems-v2]] Appendix A "Annihilation" | dp-core-2-058
Kind: C
Fidelity: variant: the countable dyadic algebra
Hyps: (a) -/
theorem dyadic_no_world_of_countable : IsEmpty (World (Jω Dy)) :=
  no_world_of_countable_atomless fun X hX =>
    let ⟨Y, h1, h2, h3⟩ := dyadic_atomless X hX
    ⟨Y, lt_of_le_of_ne h1 h3, h2⟩

end

end Cleanroom.Decision.DpWorldsJb
