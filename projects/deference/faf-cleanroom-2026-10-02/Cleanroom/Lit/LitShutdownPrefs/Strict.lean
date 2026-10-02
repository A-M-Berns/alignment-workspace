import Cleanroom.Lit.LitShutdownPrefs.Weak

/-!
# Framework S: strict behavioural preference as primitive (Thornley 2024/2025, DReST, Petersen)

`lt X Y` is primitive (Def A.1: the agent deterministically chooses `X` over `Y`). Derived:
`lacks` (stochastic choice), `sweetening`/`souring`, behavioural `indiff` (a lack of preference
sensitive to all sweetenings and sourings), `gap` (a lack insensitive to some), `le := lt ∨ indiff`,
`Complete := no gaps`.

* `simple_theorem_2024` — Thornley 2024 §6: under Completeness, if `l₂ ≻ l₁` then `s` can lack a
  preference with at most one of them. Pre-labelled **kind S** in the ledger: the behavioural
  definition of indifference already contains the transitivity instance the proof uses
  (fn `ntzo1lw9do`). `simple_theorem_2024_chain` is the chain form.
* The bridge to framework W (2024 fn `x09fuv8skd`): with a transitive weak `le`, usual
  indifference implies behavioural indifference (`indiff_of_weak_indiff`) and behavioural gap
  implies usual gap (`weak_gap_of_gap`); under the footnote's domain-richness condition
  (`DomainRich`) both are biconditionals.
-/

namespace Cleanroom.Lit.LitShutdownPrefs

namespace Strict

open Lottery

variable {T : Type}

/-- Lack of preference: the agent chooses stochastically (neither strict preference).
Source: DReST Def A.2; Thornley 2025 §6
Kind: D
Fidelity: exact -/
def lacks (lt : Lottery T → Lottery T → Prop) (X Y : Lottery T) : Prop := ¬ lt X Y ∧ ¬ lt Y X

/-- The sweetenings of `X`: lotteries preferred to `X`.
Source: Thornley 2025 §6
Kind: D
Fidelity: exact -/
def sweetening (lt : Lottery T → Lottery T → Prop) (X : Lottery T) : Set (Lottery T) :=
  {Z | lt Z X}

/-- The sourings of `X`: lotteries dispreferred to `X`.
Source: Thornley 2025 §6
Kind: D
Fidelity: exact -/
def souring (lt : Lottery T → Lottery T → Prop) (X : Lottery T) : Set (Lottery T) :=
  {Z | lt X Z}

/-- **Behavioural indifference**: a lack of preference sensitive to all sweetenings and sourings —
every sweetening of `X` is preferred to `Y`, every sweetening of `Y` to `X`, `X` to every souring
of `Y`, and `Y` to every souring of `X`.
Source: Thornley 2025 §6 (Indifference); 2024 §5
Kind: D
Fidelity: exact -/
def indiff (lt : Lottery T → Lottery T → Prop) (X Y : Lottery T) : Prop :=
  lacks lt X Y ∧ (∀ Z ∈ sweetening lt X, lt Z Y) ∧ (∀ Z ∈ sweetening lt Y, lt Z X) ∧
    (∀ Z ∈ souring lt Y, lt X Z) ∧ (∀ Z ∈ souring lt X, lt Y Z)

/-- **Preferential gap**: a lack of preference insensitive to some sweetening or souring.
Source: Thornley 2025 §6 (Preferential gap); 2024 §5
Kind: D
Fidelity: exact -/
def gap (lt : Lottery T → Lottery T → Prop) (X Y : Lottery T) : Prop :=
  lacks lt X Y ∧ ¬ indiff lt X Y

/-- Weak preference: strict preference or indifference.
Source: Thornley 2025 §6 ("weakly prefers … iff … prefers … or is indifferent")
Kind: D
Fidelity: exact -/
def le (lt : Lottery T → Lottery T → Prop) (X Y : Lottery T) : Prop := lt X Y ∨ indiff lt X Y

/-- Completeness: no preferential gaps.
Source: Thornley 2024 §6 (Completeness)
Kind: D
Fidelity: exact -/
def Complete (lt : Lottery T → Lottery T → Prop) : Prop := ∀ X Y, ¬ gap lt X Y

section simple

variable {lt : Lottery T → Lottery T → Prop}

/-- Under Completeness, a lack of preference is (behavioural) indifference.
Source: Thornley 2024 §6 ("Completeness rules out preferential gaps, so … must be indifferent")
Kind: L -/
theorem indiff_of_lacks_of_complete (hC : Complete lt) {X Y : Lottery T} (h : lacks lt X Y) :
    indiff lt X Y := by
  by_contra hn
  exact hC X Y ⟨h, hn⟩

/-- **The 2024 simple theorem**: under Completeness, if the agent prefers `l₂` to `l₁`, it cannot
lack a preference with both `s, l₁` and `s, l₂`. (Kind S: the transitivity instance is inside the
behavioural definition of indifference, fn `ntzo1lw9do`.)
Source: Thornley 2024 §6 ll. 155–178; corr-refs-2-008
Kind: S
Fidelity: exact
Hyps: (a) all -/
theorem simple_theorem_2024 (hC : Complete lt) {s l₁ l₂ : Lottery T} (h : lt l₂ l₁) :
    ¬ (lacks lt s l₁ ∧ lacks lt s l₂) := by
  rintro ⟨h1, h2⟩
  have hi := indiff_of_lacks_of_complete hC h1
  -- l₂ is a sweetening of l₁, hence preferred to s
  exact h2.2 (hi.2.2.1 l₂ h)

open Classical in
/-- Chain form of the 2024 simple theorem: along a strictly improving chain, `s` lacks a
preference with at most one link.
Source: Thornley 2024 §6 (the `s, l₁, l₂` picture generalised)
Kind: S
Fidelity: stronger (chain of any length)
Hyps: (a) all -/
theorem simple_theorem_2024_chain (hC : Complete lt) {n : ℕ} (l : Fin n → Lottery T)
    (hl : ∀ i j, i < j → lt (l j) (l i)) (s : Lottery T) :
    (Finset.univ.filter (fun i => lacks lt s (l i))).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro i hi j hj
  rw [Finset.mem_filter] at hi hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hij
  · exact simple_theorem_2024 hC (hl i j hij) ⟨hi.2, hj.2⟩
  · exact simple_theorem_2024 hC (hl j i hij) ⟨hj.2, hi.2⟩

end simple

/-! ## Bridge to framework W (Thornley 2024 fn `x09fuv8skd`) -/

section bridge

variable {le : Lottery T → Lottery T → Prop}

/-- With transitive weak preference, usual indifference implies behavioural indifference.
Source: Thornley 2024 fn `x09fuv8skd` ("the usual definition of indifference implies my definition")
Kind: L
Fidelity: exact
Hyps: (a) all -/
theorem indiff_of_weak_indiff (hT : Weak.Transitive le) {X Y : Lottery T}
    (h : Weak.indiff le X Y) : indiff (Weak.lt le) X Y := by
  refine ⟨⟨fun h' => h'.2 h.2, fun h' => h'.2 h.1⟩, ?_, ?_, ?_, ?_⟩
  · intro Z hZ; exact Weak.pi_trans hT hZ h
  · intro Z hZ; exact Weak.pi_trans hT hZ (Weak.indiff_symm h)
  · intro Z hZ; exact Weak.ip_trans hT h hZ
  · intro Z hZ; exact Weak.ip_trans hT (Weak.indiff_symm h) hZ

/-- With transitive weak preference, a behavioural gap implies a usual gap.
Source: Thornley 2024 fn `x09fuv8skd` ("my definition of preferential gaps implies the usual definition")
Kind: L
Fidelity: exact
Hyps: (a) all -/
theorem weak_gap_of_gap (hT : Weak.Transitive le) {X Y : Lottery T}
    (h : gap (Weak.lt le) X Y) : Weak.gap le X Y := by
  obtain ⟨hl, hni⟩ := h
  have : Weak.lacks le X Y := hl
  rcases Weak.lacks_iff.mp this with hi | hg
  · exact absurd (indiff_of_weak_indiff hT hi) hni
  · exact hg

/-- **Domain richness** (the footnote's condition): whenever neither `X ≽ Y` nor `Y ≽ X`, there is a
sweetening of `X` not weakly preferred to `Y`, or a sweetening of `Y` not weakly preferred to `X`,
or a souring of `X` to which `Y` is not weakly preferred, or a souring of `Y` to which `X` is not
weakly preferred.
Source: Thornley 2024 fn `x09fuv8skd`
Kind: D
Fidelity: exact -/
def DomainRich (le : Lottery T → Lottery T → Prop) : Prop :=
  ∀ X Y, ¬ le X Y → ¬ le Y X →
    (∃ Z, Weak.lt le Z X ∧ ¬ le Z Y) ∨ (∃ Z, Weak.lt le Z Y ∧ ¬ le Z X) ∨
      (∃ Z, Weak.lt le X Z ∧ ¬ le Y Z) ∨ (∃ Z, Weak.lt le Y Z ∧ ¬ le X Z)

/-- Under transitivity and domain richness, behavioural indifference implies usual indifference —
so the two notions are biconditional.
Source: Thornley 2024 fn `x09fuv8skd` ("the usual definition of indifference is biconditional with my definition")
Kind: L
Fidelity: exact
Hyps: (a) all (DomainRich is the footnote's own hypothesis, named) -/
theorem weak_indiff_iff_indiff (hT : Weak.Transitive le) (hD : DomainRich le) (X Y : Lottery T) :
    Weak.indiff le X Y ↔ indiff (Weak.lt le) X Y := by
  refine ⟨indiff_of_weak_indiff hT, fun h => ?_⟩
  by_contra hn
  have hl : Weak.lacks le X Y := h.1
  rcases Weak.lacks_iff.mp hl with hi | hg
  · exact hn hi
  · rcases hD X Y hg.1 hg.2 with ⟨Z, hZ, hZ'⟩ | ⟨Z, hZ, hZ'⟩ | ⟨Z, hZ, hZ'⟩ | ⟨Z, hZ, hZ'⟩
    · exact hZ' (h.2.1 Z hZ).1
    · exact hZ' (h.2.2.1 Z hZ).1
    · exact hZ' (h.2.2.2.2 Z hZ).1
    · exact hZ' (h.2.2.2.1 Z hZ).1

/-- Under transitivity and domain richness, usual gaps and behavioural gaps coincide.
Source: Thornley 2024 fn `x09fuv8skd` ("the usual definition of preferential gaps is biconditional with my definition")
Kind: L
Fidelity: exact
Hyps: (a) all -/
theorem weak_gap_iff_gap (hT : Weak.Transitive le) (hD : DomainRich le) (X Y : Lottery T) :
    Weak.gap le X Y ↔ gap (Weak.lt le) X Y := by
  refine ⟨fun h => ⟨⟨fun h' => h.1 h'.1, fun h' => h.2 h'.1⟩, fun hi => ?_⟩, weak_gap_of_gap hT⟩
  have := (weak_indiff_iff_indiff hT hD X Y).mpr hi
  exact h.1 this.1

end bridge

end Strict

end Cleanroom.Lit.LitShutdownPrefs
