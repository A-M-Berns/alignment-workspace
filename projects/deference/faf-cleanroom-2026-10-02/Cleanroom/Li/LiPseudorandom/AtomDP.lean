import Cleanroom.Li.LiPseudorandom.Defs
import LogicalInduction.Construction.LIA
import LogicalInduction.Properties.Calibration
import LogicalInduction.Framework.Machine.Witnesses

/-!
# `li-pseudorandom` — T6.1–T6.2: the atom-deciding process and LIA locality

* Membership in the stages of `atomDP a x g` (`literalOf_mem_atomDP`, `atom_mem_atomDP_iff`,
  `neg_atom_mem_atomDP_iff`): `atom (a n) ∈ D m ↔ g n ≤ m ∧ x n` under `Function.Injective a`
  and `∀ j, j < g j`.
* The `thm:benford` side conditions for this process: `atomDP_hworld` (every stage has a
  consistent world — the atom world `atomWorld a x`, so the process is not vacuously an inductor's
  process), `atomDP_theoryTruth` (`TheoryTruth (atomFamily a) (atomDP a x g) (truthR x)`, derived
  from the stages, never assumed) and `machineSentenceCodes_atomFamily_id` (FAF's
  `machineSentenceCodes_atom` for `a = id`; general `a` is a parameter dependents discharge).
* Stage locality `atomDP_D_congr` and **LIA locality** `liaStates_congr`: two processes agreeing
  on stages `≤ n` have the same LIA state at day `n` (strong induction through FAF's
  `TradingFirmAtFromStages_eq_of_eq_prefix`). Corollary `liaHistory_atomDP_causal`: the builder
  `x ↦ liaHistory (atomDP a x g)` is causal for delay `g` in the sense of T5.

Not in FAF (grep 2026-09-29): no locality lemma for `liaStates`; the `_eq_of_eq_prefix` family
(`Construction/TradingFirm.lean`) does the stage-level work and is used here.
-/

namespace Cleanroom.Li.LiPseudorandom

open LogicalInduction LO.Propositional

/-! ## Membership in the stages -/

/-- Unfolded membership: `φ ∈ D n` iff `φ` is the literal of some `j ≤ n` with `g j ≤ n`.
Source: mandate T6.1
Kind: L
Fidelity: exact -/
lemma mem_atomDP_iff {a : ℕ → ℕ} {x : ℕ → Bool} {g : ℕ → ℕ} {n : ℕ} {φ : Sentence} :
    φ ∈ (atomDP a x g).D n ↔ ∃ j, (j ≤ n ∧ g j ≤ n) ∧ literalOf a x j = φ := by
  simp only [atomDP, Finset.mem_image, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

/-- The literal of member `j` is revealed at every stage `≥ g j` (given `j < g j`).
Source: mandate T6.1
Kind: L
Fidelity: exact -/
lemma literalOf_mem_atomDP {a : ℕ → ℕ} {x : ℕ → Bool} {g : ℕ → ℕ} (hg : ∀ j, j < g j)
    {j n : ℕ} (hjn : g j ≤ n) : literalOf a x j ∈ (atomDP a x g).D n :=
  mem_atomDP_iff.2 ⟨j, ⟨(hg j).le.trans hjn, hjn⟩, rfl⟩

/-- A negated atom is never an atom (Foundation: `∼φ = φ 🡒 ⊥`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma neg_atom_ne_atom (i k : ℕ) : (∼(Formula.atom i : Sentence)) ≠ Formula.atom k := by
  intro h
  have h' : Formula.imp (Formula.atom i) Formula.falsum = Formula.atom k := h
  cases h'

/-- **Decided-with-delay, positive form.** Under `Function.Injective a` and `∀ j, j < g j`:
`atom (a n) ∈ (atomDP a x g).D m ↔ g n ≤ m ∧ x n = true`.
Source: mandate T6.1 (decided-with-delay facts); [[bli-program]] §3.2(b), §3.6(iii)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem atom_mem_atomDP_iff {a : ℕ → ℕ} (ha : Function.Injective a) {x : ℕ → Bool} {g : ℕ → ℕ}
    (hg : ∀ j, j < g j) {n m : ℕ} :
    (Formula.atom (a n) : Sentence) ∈ (atomDP a x g).D m ↔ g n ≤ m ∧ x n = true := by
  rw [mem_atomDP_iff]
  constructor
  · rintro ⟨j, ⟨_, hgj⟩, hlit⟩
    unfold literalOf at hlit
    by_cases hx : x j = true
    · rw [if_pos hx] at hlit
      have hjn : j = n := ha (Formula.atom.inj hlit)
      subst hjn
      exact ⟨hgj, hx⟩
    · rw [if_neg hx] at hlit
      exact absurd hlit (neg_atom_ne_atom _ _)
  · rintro ⟨hgn, hx⟩
    refine ⟨n, ⟨(hg n).le.trans hgn, hgn⟩, ?_⟩
    simp [literalOf, hx]

/-- **Decided-with-delay, negative form.** Under `Function.Injective a` and `∀ j, j < g j`:
`∼atom (a n) ∈ (atomDP a x g).D m ↔ g n ≤ m ∧ x n = false`.
Source: mandate T6.1 (decided-with-delay facts)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem neg_atom_mem_atomDP_iff {a : ℕ → ℕ} (ha : Function.Injective a) {x : ℕ → Bool}
    {g : ℕ → ℕ} (hg : ∀ j, j < g j) {n m : ℕ} :
    (∼(Formula.atom (a n) : Sentence)) ∈ (atomDP a x g).D m ↔ g n ≤ m ∧ x n = false := by
  rw [mem_atomDP_iff]
  constructor
  · rintro ⟨j, ⟨_, hgj⟩, hlit⟩
    unfold literalOf at hlit
    by_cases hx : x j = true
    · rw [if_pos hx] at hlit
      exact absurd hlit.symm (neg_atom_ne_atom _ _)
    · rw [if_neg hx] at hlit
      have hlit' : Formula.imp (Formula.atom (a j)) Formula.falsum =
          Formula.imp (Formula.atom (a n)) Formula.falsum := hlit
      have hjn : j = n := ha (Formula.atom.inj (Formula.imp.inj hlit').1)
      subst hjn
      exact ⟨hgj, by simpa using hx⟩
  · rintro ⟨hgn, hx⟩
    refine ⟨n, ⟨(hg n).le.trans hgn, hgn⟩, ?_⟩
    simp [literalOf, hx]

/-! ## The side conditions of `thm:benford` -/

/-- The atom world of `(a, x)`: atom `i` is true iff it is `a j` for some `j` with `x j`.
Source: mandate T6.1 (`hworld` witness)
Kind: D
Fidelity: exact -/
def atomWorld (a : ℕ → ℕ) (x : ℕ → Bool) : PCWorld := fun i => ∃ j, a j = i ∧ x j = true

/-- The atom world is consistent with every stage of `atomDP a x g` when `a` is injective.
Source: mandate T6.1
Kind: L
Fidelity: exact
Hyps: (a) -/
lemma atomWorld_consistentWith {a : ℕ → ℕ} (ha : Function.Injective a) (x : ℕ → Bool)
    (g : ℕ → ℕ) (n : ℕ) : (atomWorld a x).ConsistentWith ((atomDP a x g).D n) := by
  intro φ hφ
  obtain ⟨j, -, rfl⟩ := mem_atomDP_iff.1 hφ
  unfold literalOf
  split_ifs with hx
  · exact ⟨j, rfl, hx⟩
  · rw [PCWorld.holds_neg, PCWorld.holds_atom]
    rintro ⟨j', hj', hx'⟩
    have := ha hj'
    subst this
    simp_all

/-- **`hworld` for `atomDP`**: every stage has a consistent world (the atom world), so the process
is not vacuously an inductor's process (`isLogicalInductor_of_stage_unsatisfiable` does not
apply). A side condition derived from the stages; the non-vacuity role is a remark, not a witness
of a headline's hypothesis package.
Source: mandate T6.1; FAF `thm:benford` caller obligation
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem atomDP_hworld {a : ℕ → ℕ} (ha : Function.Injective a) (x : ℕ → Bool) (g : ℕ → ℕ) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((atomDP a x g).D n) :=
  fun n => ⟨atomWorld a x, atomWorld_consistentWith ha x g n⟩

/-- **`TheoryTruth` for `atomDP`**, derived from the stages: every world consistent with the
completed theory pays `truthR x n` on `atom (a n)`, because the literal of `n` is in stage `g n`.
Source: mandate T6.1; FAF `AffineCombination.TheoryTruth`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem atomDP_theoryTruth {a : ℕ → ℕ} {g : ℕ → ℕ} (hg : ∀ j, j < g j) (x : ℕ → Bool) :
    AffineCombination.TheoryTruth (atomFamily a) (atomDP a x g) (truthR x) := by
  intro n v hv
  have hmem := hv (g n) _ (literalOf_mem_atomDP (a := a) (x := x) hg (le_refl (g n)))
  unfold atomFamily truthR PCWorld.payout
  unfold literalOf at hmem
  by_cases hx : x n = true
  · rw [if_pos hx] at hmem
    simp [hx, hmem]
  · have hx' : x n = false := by simpa using hx
    rw [if_neg (by simp [hx'])] at hmem
    rw [PCWorld.holds_neg] at hmem
    simp [hx', hmem]

/-- **`MachineSentenceCodes (atomFamily id)`**: FAF's `machineSentenceCodes_atom`. For a general
placement `a` the certificate is a parameter that dependents discharge with their allocator's.
Source: FAF `machineSentenceCodes_atom` (`Framework/Machine/Witnesses.lean`)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem machineSentenceCodes_atomFamily_id : MachineSentenceCodes (atomFamily id) :=
  machineSentenceCodes_atom

/-! ## Locality -/

/-- Stages `≤ n` of `atomDP` read only the truth values decided by day `n`.
Source: mandate T6.2
Kind: L
Fidelity: exact
Hyps: (a) -/
lemma atomDP_D_congr {a : ℕ → ℕ} {x y : ℕ → Bool} {g : ℕ → ℕ} {n : ℕ}
    (h : ∀ j, g j ≤ n → x j = y j) : ∀ m ≤ n, (atomDP a x g).D m = (atomDP a y g).D m := by
  intro m hm
  simp only [atomDP]
  apply Finset.image_congr
  intro j hj
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at hj
  unfold literalOf
  rw [h j (hj.2.trans hm)]

/-- **LIA locality.** Two deductive processes agreeing on every stage `≤ n` have the same LIA
state at day `n`. Strong induction on the day: the past states agree by the induction hypothesis,
and the realized trading firm's day-`n` action depends on the process only through stages `≤ n`
(FAF's `TradingFirmAtFromStages_eq_of_eq_prefix`).
Source: mandate T6.2; FAF `liaStates`, `TradingFirmAtFromStages_eq_of_eq_prefix`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem liaStates_congr {DP DP' : DeductiveProcess} :
    ∀ n, (∀ m ≤ n, DP.D m = DP'.D m) → liaStates DP n = liaStates DP' n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hD
    have hpast : (List.ofFn fun i : Fin n => liaStates DP i) =
        List.ofFn fun i : Fin n => liaStates DP' i := by
      apply List.ext_getElem
      · simp
      · intro i hi₁ hi₂
        simp only [List.getElem_ofFn]
        have hi : i < n := by simpa using hi₁
        exact ih i hi (fun m hm => hD m (by omega))
    have hT : ∀ Q, TradingFirmAt DP Q n = TradingFirmAt DP' Q n := by
      intro Q
      rw [← TradingFirmAtFromStages_eq_of_eq_prefix DP DP'.D Q n (fun m hm => (hD m hm).symm),
        ← TradingFirmAtFromStages_eq_of_eq_prefix DP' DP'.D Q n (fun _ _ => rfl)]
    conv_lhs => rw [liaStates]
    conv_rhs => rw [liaStates]
    change MarketMaker
        ((TradingFirm DP).action n (List.ofFn fun i : Fin n => liaStates DP i))
        (List.ofFn fun i : Fin n => liaStates DP i)
        (marketMakerError n) (marketMakerError_pos n) =
      MarketMaker
        ((TradingFirm DP').action n (List.ofFn fun i : Fin n => liaStates DP' i))
        (List.ofFn fun i : Fin n => liaStates DP' i)
        (marketMakerError n) (marketMakerError_pos n)
    rw [hpast]
    show MarketMaker (TradingFirmAt DP _ n) _ _ _ = MarketMaker (TradingFirmAt DP' _ n) _ _ _
    rw [hT]

/-- **LIA locality, market form.** Processes agreeing on stages `≤ n` have the same LIA prices
at every day `≤ n`.
Source: mandate T6.2
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem liaHistory_congr {DP DP' : DeductiveProcess} {n : ℕ} (hD : ∀ m ≤ n, DP.D m = DP'.D m) :
    ∀ m ≤ n, ∀ φ, liaHistory DP m φ = liaHistory DP' m φ := by
  intro m hm φ
  simp only [liaHistory]
  rw [liaStates_congr m (fun m' hm' => hD m' (hm'.trans hm))]

/-- **The LIA over `atomDP` is a causal builder for delay `g`**: its prices at days `≤ n` depend
only on the truth values `x j` with `g j ≤ n`. This is what lets T5 apply to the family of
record (`Family.lean`). Two lemma applications (`atomDP_D_congr`, `liaHistory_congr`); the
content is in `liaStates_congr`.
Source: mandate T6.2 (corollary); T5
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem liaHistory_atomDP_causal (a g : ℕ → ℕ) :
    CausalBuilder (fun x => liaHistory (atomDP a x g)) g := by
  intro x y n h m hm φ
  exact liaHistory_congr (atomDP_D_congr (a := a) h) m hm φ

end Cleanroom.Li.LiPseudorandom
