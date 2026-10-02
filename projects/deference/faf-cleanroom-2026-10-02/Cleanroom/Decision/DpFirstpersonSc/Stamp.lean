import Cleanroom.Decision.DpFaithfulUdt.Pdc
import Cleanroom.Decision.DpFirstpersonSc.Bridge

/-!
# The occurrence-stamped problem `B^{pol}` (decision 2 of [[dp-firstperson-sc-mandate]])

`firstperson.md` D1/D2: the enriched algebra `𝓔^U` adds coordinates `pol_d ∈ A_d ∪ {⊥}` for
`d ∈ U`; the stamped problem `B^{pol}` is the same tree with each leaf-world carrying the action
drawn at the `d`-node on its path (`⊥` if none). Here that is a **re-worlding**, not a relocation:
`stamp U B := relabel B (fun ℓ => (world B ℓ, fun d : ↥U => lastDraw d B ℓ))` over the worlds
`SW Ω acts U := Ω × ((d : ↥U) → Option (acts d))`, with `dp-calibration`'s `relabel` (same tree,
same run law: `leafLaw_relabel`).

* `lastDraw d B ℓ : Option (acts d)` is the **last** `d`-draw on the path to `ℓ` (`none` iff
  `count d B ℓ = 0`, `lastDraw_eq_none_iff`). D2 says the coordinate is "well-defined iff
  `#_d ≤ 1`"; on that domain the last draw is *the* draw (`lastDraw_eq_some_iff_of_le_one`:
  `pol_d = some a ↔ ⟨d,a⟩ ∈ draws`), so this is a `variant` that agrees with D2 on D2's domain
  and extends it off it. **No stamped headline needs `AlmostFair`**: the audit reads only
  `occW := {pol_d ≠ ⊥}`, which is `{#_d > 0}` on every tree (`mem_worldEv_stamp_occW`).
* `occW U hd` is the world event `{pol_d ≠ ⊥}` of the stamped problem and
  `worldEv (stamp U B) (occW U hd)` is `occ d B` transported along the leaf equivalence
  (`mem_worldEv_stamp_occW`): **`occ(d)` is a world event of the stamped problem, for every
  tree** — the fact FP-21′(iii) and D7′ rest on.
* `obsW U X := Prod.fst ⁻¹ X` is a base event read on the stamped carrier.
* The transport lemmas `nu_stamp_obsW_inter_occW`, `nu_stamp_occW`, `nu_stamp_obsW`,
  `paySum_stamp_obsW_inter_occW` turn the stamped `ν`/payoff masses into `dp-core-tree` masses on
  `B` (`occEv`/`occPay` are `dp-faithful-udt`'s, `Pdc.lean`).

Why not `dp-faithful-udt`'s `relocRoot`/`polEv`: `RW` assigns a disposition on every run and has
no `⊥`, so `occ(d)` is not expressible there (mandate decision 2); the relation "on `occ(d)`,
`pol_d` = the drawn act" is `lastDraw_eq_some_iff_of_le_one`, a lemma, not an identification.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} {acts : ι → Type} [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
  [DecidableEq ι]

/-! ## The stamped worlds and the last draw -/

/-- **The stamped worlds `𝓔^U`** (D1): a base world and, for each `d ∈ U`, the coordinate
`pol_d ∈ A_d ∪ {⊥}` rendered as `Option (acts d)` (`none` = `⊥`).
Source: `firstperson.md` D1 ("`𝓔^U := 𝓔` plus coordinates `pol_d ∈ A_d ∪ {⊥}`, `d ∈ U`")
Kind: D
Fidelity: exact (finite atomic carrier) -/
abbrev SW (Ω : Type) (acts : ι → Type) (U : Finset ι) : Type :=
  Ω × ((d : ↥U) → Option (acts d.1))

/-- **The last `d`-draw on the path to a leaf** (`none` iff the path has no `d`-node).
Source: `firstperson.md` D2 ("the action drawn at the `d`-node on its path (`⊥` if none)")
Kind: D
Fidelity: variant: under nesting the coordinate is the *last* draw; D2 says "well-defined iff
`#_d ≤ 1`", and on that domain this is the unique draw (`lastDraw_eq_some_iff_of_le_one`) -/
def lastDraw (d : ι) : (B : Tree Ω ι acts K) → B.Leaves → Option (acts d)
  | .leaf _ _, _ => none
  | .chance _ _ child, ⟨i, ℓ⟩ => lastDraw d (child i) ℓ
  | .decision d' child, ⟨a, ℓ⟩ =>
      match lastDraw d (child a) ℓ with
      | some a' => some a'
      | none => if h : d' = d then some (h ▸ a) else none

/-- Equation lemma at a chance node. Source: none: infrastructure. Kind: L -/
@[simp] theorem lastDraw_chance (d : ι) {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) (i : Fin n) (ℓ : (child i).Leaves) :
    lastDraw d (.chance n β child) ⟨i, ℓ⟩ = lastDraw d (child i) ℓ := rfl

/-- Equation lemma at a decision node of another point. Source: none: infrastructure. Kind: L -/
theorem lastDraw_decision_ne (d d' : ι) (child : acts d' → Tree Ω ι acts K) (a : acts d')
    (ℓ : (child a).Leaves) (h : d' ≠ d) :
    lastDraw d (.decision d' child) ⟨a, ℓ⟩ = lastDraw d (child a) ℓ := by
  show (match lastDraw d (child a) ℓ with
    | some a' => some a'
    | none => if h : d' = d then some (h ▸ a) else none) = _
  cases hl : lastDraw d (child a) ℓ with
  | none => simp [h]
  | some a' => rfl

/-- Equation lemma at a `d`-node: the last draw below if any, else this node's draw.
Source: none: infrastructure. Kind: L -/
theorem lastDraw_decision_self (d : ι) (child : acts d → Tree Ω ι acts K) (a : acts d)
    (ℓ : (child a).Leaves) :
    lastDraw d (.decision d child) ⟨a, ℓ⟩ =
      (lastDraw d (child a) ℓ).elim (some a) some := by
  show (match lastDraw d (child a) ℓ with
    | some a' => some a'
    | none => if h : d = d then some (h ▸ a) else none) = _
  cases hl : lastDraw d (child a) ℓ with
  | none => simp
  | some a' => rfl

/-- **`pol_d = ⊥` iff the path has no `d`-node** (`#_d = 0`), on every tree.
Source: `firstperson.md` D2, D7′ (`occ(d) = {pol_d ≠ ⊥}`)
Kind: P
Fidelity: exact
Hyps: none -/
theorem lastDraw_eq_none_iff (d : ι) :
    (B : Tree Ω ι acts K) → ∀ ℓ, lastDraw d B ℓ = none ↔ count d B ℓ = 0
  | .leaf _ _, _ => by simp [lastDraw, count]
  | .chance _ _ child, ⟨i, ℓ⟩ => by
      rw [lastDraw_chance, count_chance]
      exact lastDraw_eq_none_iff d (child i) ℓ
  | .decision d' child, ⟨a, ℓ⟩ => by
      rw [count_decision]
      by_cases h : d' = d
      · subst h
        rw [lastDraw_decision_self, if_pos rfl]
        cases hl : lastDraw d' (child a) ℓ <;> simp
      · rw [lastDraw_decision_ne d d' child a ℓ h, if_neg h, zero_add]
        exact lastDraw_eq_none_iff d (child a) ℓ

/-- A `d`-draw on the path makes `#_d` positive. Source: none: infrastructure. Kind: L -/
theorem count_pos_of_mem_draws (d : ι) (a : acts d) :
    (B : Tree Ω ι acts K) → ∀ ℓ, (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ → 0 < count d B ℓ
  | .leaf _ _, _, h => by simp [draws] at h
  | .chance _ _ child, ⟨i, ℓ⟩, h => by
      rw [count_chance]; exact count_pos_of_mem_draws d a (child i) ℓ h
  | .decision d' child, ⟨a', ℓ⟩, h => by
      rw [count_decision]
      simp only [draws, List.mem_cons] at h
      rcases h with h | h
      · have : d' = d := (Sigma.mk.inj_iff.mp h.symm).1
        rw [if_pos this]; omega
      · have := count_pos_of_mem_draws d a (child a') ℓ h
        split_ifs <;> omega

/-- **On D2's domain the coordinate is the draw**: when `#_d ≤ 1` on the path,
`pol_d = some a ↔ ⟨d, a⟩ ∈ draws`.
Source: `firstperson.md` D2 ("well-defined iff `#_d ≤ 1`"); D3 (`ρ_d(a) := {pol_d = a}`)
Kind: P
Fidelity: exact on D2's domain
Hyps: (a) `count d B ℓ ≤ 1` -/
theorem lastDraw_eq_some_iff_of_le_one (d : ι) (a : acts d) :
    (B : Tree Ω ι acts K) → ∀ ℓ, count d B ℓ ≤ 1 →
      (lastDraw d B ℓ = some a ↔ (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ)
  | .leaf _ _, _, _ => by simp [lastDraw, draws]
  | .chance _ _ child, ⟨i, ℓ⟩, h => by
      rw [lastDraw_chance]
      exact lastDraw_eq_some_iff_of_le_one d a (child i) ℓ (by rwa [count_chance] at h)
  | .decision d' child, ⟨a', ℓ⟩, h => by
      rw [count_decision] at h
      simp only [draws, List.mem_cons]
      by_cases hd : d' = d
      · subst hd
        rw [if_pos rfl] at h
        have h0 : count d' (child a') ℓ = 0 := by omega
        rw [lastDraw_decision_self, (lastDraw_eq_none_iff d' (child a') ℓ).mpr h0]
        simp only [Option.elim, Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and]
        constructor
        · intro e; exact Or.inl e.symm
        · rintro (e | e)
          · exact e.symm
          · exact absurd (count_pos_of_mem_draws d' a (child a') ℓ e) (by omega)
      · rw [if_neg hd, zero_add] at h
        rw [lastDraw_decision_ne d d' child a' ℓ hd,
          lastDraw_eq_some_iff_of_le_one d a (child a') ℓ h]
        constructor
        · intro e; exact Or.inr e
        · rintro (e | e)
          · exact absurd (Sigma.mk.inj_iff.mp e).1.symm hd
          · exact e

/-! ## The stamped problem -/

variable [Fintype Ω] [DecidableEq Ω]

/-- The stamping map on leaves: `ℓ ↦ (λ(ℓ), (pol_d(ℓ))_{d ∈ U})`.
Source: `firstperson.md` D2
Kind: D -/
def stampWorld (U : Finset ι) (B : Tree Ω ι acts K) (ℓ : B.Leaves) : SW Ω acts U :=
  (world B ℓ, fun d => lastDraw d.1 B ℓ)

/-- **The stamped problem `B^{pol}`** (D2): the same tree, re-worlded by `stampWorld`.
Source: `firstperson.md` D2 ("Same tree; each leaf-world carries `pol_d`")
Kind: D
Fidelity: variant: the coordinate is the last draw (see `lastDraw`); exact on D2's domain -/
def stamp (U : Finset ι) (B : Tree Ω ι acts K) : Tree (SW Ω acts U) ι acts K :=
  relabel B (stampWorld U B)

/-- The leaves of the stamped problem are the leaves of `B`. Source: none: infrastructure.
Kind: D -/
def stampLeaves (U : Finset ι) (B : Tree Ω ι acts K) : (stamp U B).Leaves ≃ B.Leaves :=
  relabelLeaves B (stampWorld U B)

/-- The world at a stamped leaf. Source: none: infrastructure. Kind: L -/
theorem world_stamp (U : Finset ι) (B : Tree Ω ι acts K) (ℓ' : (stamp U B).Leaves) :
    world (stamp U B) ℓ' = stampWorld U B (stampLeaves U B ℓ') :=
  world_relabel B (stampWorld U B) ℓ'

/-- The run law is unchanged by stamping. Source: `firstperson.md` D2 ("same tree"). Kind: L -/
theorem leafLaw_stamp (U : Finset ι) (C : Proc ι acts K) (B : Tree Ω ι acts K)
    (ℓ' : (stamp U B).Leaves) :
    leafLaw C (stamp U B) ℓ' = leafLaw C B (stampLeaves U B ℓ') :=
  leafLaw_relabel C B (stampWorld U B) ℓ'

/-- Payoffs are unchanged by stamping. Source: none: infrastructure. Kind: L -/
theorem payoff_stamp (U : Finset ι) (B : Tree Ω ι acts K) (ℓ' : (stamp U B).Leaves) :
    payoff (stamp U B) ℓ' = payoff B (stampLeaves U B ℓ') :=
  payoff_relabel B (stampWorld U B) ℓ'

/-- Queried points are unchanged by stamping. Source: none: infrastructure. Kind: L -/
theorem queried_stamp (U : Finset ι) (B : Tree Ω ι acts K) : queried (stamp U B) = queried B :=
  queried_relabel B (stampWorld U B)

/-- `#_d` is unchanged by stamping. Source: none: infrastructure. Kind: L -/
theorem count_stamp (U : Finset ι) (d : ι) (B : Tree Ω ι acts K) (ℓ' : (stamp U B).Leaves) :
    count d (stamp U B) ℓ' = count d B (stampLeaves U B ℓ') :=
  count_relabel d B (stampWorld U B) ℓ'

/-- **`occW`: the occurrence event `{pol_d ≠ ⊥}`** of the stamped algebra, for `d ∈ U`.
Source: `firstperson.md` D7′ ("`occ(d) = {pol_d ≠ ⊥}` is an event of the state algebra")
Kind: D
Fidelity: exact -/
def occW (U : Finset ι) {d : ι} (hd : d ∈ U) : Finset (SW Ω acts U) :=
  Finset.univ.filter fun w => w.2 ⟨d, hd⟩ ≠ none

/-- A base event read on the stamped carrier: `Prod.fst ⁻¹ X`.
Source: `firstperson.md` D1 (`𝓔 ⊆ 𝓔^U`, the base events)
Kind: D -/
def obsW (U : Finset ι) (X : Finset Ω) : Finset (SW Ω acts U) :=
  Finset.univ.filter fun w => w.1 ∈ X

/-- Membership in `occW`. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_occW (U : Finset ι) {d : ι} (hd : d ∈ U) (w : SW Ω acts U) :
    w ∈ occW U hd ↔ w.2 ⟨d, hd⟩ ≠ none := by simp [occW]

/-- Membership in `obsW`. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_obsW (U : Finset ι) (X : Finset Ω) (w : SW Ω acts U) :
    w ∈ obsW U X ↔ w.1 ∈ X := by simp [obsW]

/-- **`occ(d)` is a world event of the stamped problem**: a stamped leaf lies in
`{λ' ⊨ occW}` iff its base leaf lies in `occ d B` — for every tree.
Source: `firstperson.md` D7′, FP-21′(iii) ("on `𝓔^U` … it is `{pol_d ≠ ⊥}`")
Kind: P
Fidelity: exact (no `AlmostFair` needed: `occW` reads only whether a `d`-draw exists)
Hyps: none -/
theorem mem_worldEv_stamp_occW (U : Finset ι) {d : ι} (hd : d ∈ U) (B : Tree Ω ι acts K)
    (ℓ' : (stamp U B).Leaves) :
    ℓ' ∈ worldEv (stamp U B) (occW U hd) ↔ stampLeaves U B ℓ' ∈ occ d B := by
  simp only [worldEv, Finset.mem_filter, Finset.mem_univ, true_and, mem_occW, world_stamp,
    stampWorld, occ]
  rw [ne_eq, lastDraw_eq_none_iff]
  exact Nat.pos_iff_ne_zero.symm

/-- A base event on the stamped problem is the base event on `B`.
Source: none: infrastructure. Kind: L -/
theorem mem_worldEv_stamp_obsW (U : Finset ι) (X : Finset Ω) (B : Tree Ω ι acts K)
    (ℓ' : (stamp U B).Leaves) :
    ℓ' ∈ worldEv (stamp U B) (obsW U X) ↔ stampLeaves U B ℓ' ∈ worldEv B X := by
  simp [worldEv, world_stamp, stampWorld]

/-! ## Transport of masses -/

/-- A sum over a finset as an indicator sum over the type. Source: none: infrastructure.
Kind: L -/
theorem sum_eq_sum_ite_mem {β M : Type} [Fintype β] [DecidableEq β] [AddCommMonoid M]
    (S : Finset β) (f : β → M) : ∑ x ∈ S, f x = ∑ x, if x ∈ S then f x else 0 := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

section transport

variable [∀ d, Nonempty (acts d)] (U : Finset ι) (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- `ν` on the stamped problem as a sum over the base leaves.
Source: none: infrastructure. Kind: L -/
theorem nu_stamp_eq_sum (Y : Finset (SW Ω acts U)) :
    nu C (stamp U B) Y = ∑ ℓ, if stampWorld U B ℓ ∈ Y then leafLaw C B ℓ else 0 := by
  rw [nu_eq_sum]
  exact Fintype.sum_equiv (stampLeaves U B) _ _ fun ℓ' => by rw [world_stamp, leafLaw_stamp]

/-- The payoff mass on the stamped problem as a sum over the base leaves.
Source: none: infrastructure. Kind: L -/
theorem paySum_stamp_eq_sum (Y : Finset (SW Ω acts U)) :
    paySum C (stamp U B) Y =
      ∑ ℓ, if stampWorld U B ℓ ∈ Y then leafLaw C B ℓ * payoff B ℓ else 0 := by
  rw [paySum_eq_sum_ite]
  exact Fintype.sum_equiv (stampLeaves U B) _ _ fun ℓ' => by
    rw [world_stamp, leafLaw_stamp, payoff_stamp]

/-- `stampWorld ℓ ∈ occW ↔ ℓ ∈ occ d B`. Source: none: infrastructure. Kind: L -/
theorem stampWorld_mem_occW {d : ι} (hd : d ∈ U) (ℓ : B.Leaves) :
    stampWorld U B ℓ ∈ occW U hd ↔ ℓ ∈ occ d B := by
  simp only [mem_occW, stampWorld, occ, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [ne_eq, lastDraw_eq_none_iff]
  exact Nat.pos_iff_ne_zero.symm

/-- `stampWorld ℓ ∈ obsW X ↔ ℓ ∈ worldEv B X`. Source: none: infrastructure. Kind: L -/
theorem stampWorld_mem_obsW (X : Finset Ω) (ℓ : B.Leaves) :
    stampWorld U B ℓ ∈ obsW U X ↔ ℓ ∈ worldEv B X := by
  simp [stampWorld, worldEv]

/-- **`ν'(X ∧ occ(d)) = μ({λ ⊨ X} ∩ occ(d))`**: the stamped mass of a base event on the
occurrence is `dp-faithful-udt`'s `occEv` mass.
Source: `firstperson.md` D7′ (the referent's numerator)
Kind: L -/
theorem nu_stamp_obsW_inter_occW {d : ι} (hd : d ∈ U) (X : Finset Ω) :
    nu C (stamp U B) (obsW U X ∩ occW U hd) = mass C B (occEv B d X) := by
  rw [nu_stamp_eq_sum]
  unfold mass
  rw [sum_eq_sum_ite_mem (occEv B d X)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [occEv, Finset.mem_inter, stampWorld_mem_obsW, stampWorld_mem_occW]

/-- `ν'(occ(d)) = μ(occ(d))`. Source: `firstperson.md` D7′. Kind: L -/
theorem nu_stamp_occW {d : ι} (hd : d ∈ U) :
    nu C (stamp U B) (occW U hd) = mass C B (occ d B) := by
  have := nu_stamp_obsW_inter_occW U C B hd Finset.univ
  rw [occEv_univ] at this
  rw [← this]
  congr 1
  ext w; simp

/-- `ν'(X) = ν(X)` for a base event. Source: none: infrastructure. Kind: L -/
theorem nu_stamp_obsW (X : Finset Ω) : nu C (stamp U B) (obsW U X) = nu C B X := by
  rw [nu_stamp_eq_sum, nu_eq_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [stampWorld_mem_obsW, worldEv, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The stamped payoff mass of `X ∧ occ(d)` is `occPay`. Source: none: infrastructure. Kind: L -/
theorem paySum_stamp_obsW_inter_occW {d : ι} (hd : d ∈ U) (X : Finset Ω) :
    paySum C (stamp U B) (obsW U X ∩ occW U hd) = occPay C B d X := by
  rw [paySum_stamp_eq_sum]
  unfold occPay
  rw [sum_eq_sum_ite_mem (occEv B d X)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [occEv, Finset.mem_inter, stampWorld_mem_obsW, stampWorld_mem_occW]

/-- The stamped mass of a difference of a base event and the occurrence.
Source: none: infrastructure. Kind: L -/
theorem nu_stamp_obsW_sdiff_occW {d : ι} (hd : d ∈ U) (X : Finset Ω) :
    nu C (stamp U B) (obsW U X \ occW U hd) = mass C B (worldEv B X \ occ d B) := by
  rw [nu_stamp_eq_sum]
  unfold mass
  rw [sum_eq_sum_ite_mem (worldEv B X \ occ d B)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [Finset.mem_sdiff, stampWorld_mem_obsW, stampWorld_mem_occW]

/-- The stamped mass of the occurrence minus a base event.
Source: none: infrastructure. Kind: L -/
theorem nu_stamp_occW_sdiff_obsW {d : ι} (hd : d ∈ U) (X : Finset Ω) :
    nu C (stamp U B) (occW U hd \ obsW U X) = mass C B (occ d B \ worldEv B X) := by
  rw [nu_stamp_eq_sum]
  unfold mass
  rw [sum_eq_sum_ite_mem (occ d B \ worldEv B X)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [Finset.mem_sdiff, stampWorld_mem_obsW, stampWorld_mem_occW]

end transport

end Cleanroom.Decision.DpFirstpersonSc
