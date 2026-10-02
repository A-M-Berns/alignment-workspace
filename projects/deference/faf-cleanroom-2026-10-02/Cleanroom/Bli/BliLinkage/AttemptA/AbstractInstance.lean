import Cleanroom.Bli.BliLinkage.AttemptA.Determination
import Cleanroom.Bli.BliTrajectory.Coherent

/-!
# `bli-linkage`, attempt A — the abstract instance for the trilemma witnesses

A cell-literal family whose literals partition by **Boolean logic alone**: two cells, cell `0`
the atom `#(litCode m c)` and cell `1` its negation, so `excl`/`exh` hold in *every* world and
over *every* process (`boolFamily`). The witnesses live over the empty process `emptyDP` (stages
decide nothing, so stage-worlds are free — the mandate's "abstract `DP` whose stages decide
nothing about the literals"), one coordinate `c₀ = ⌜cohAtom⌝` (`bli-trajectory`'s `Formula.atom 0`,
small from day `1`), two tables `tbl0`/`tbl1` placing it in cell `0`/`1`, representatives
`(ρ₀, ρ₁)`, and the four valuations `wAll`/`wLit`/`wCoh`/`wNone` (every literal atom true or
false × the coordinate true or false), mixed by `mix4`. Everything the predicates read is computed
by `simp` on these four worlds.

Disclosure: this is an abstract (non-inductor) base, as the mandate's sharpness witness is
("the trajectory prior run backwards"; program §7 item 10). The B2 instantiation of K1/K2 over
FAF's `paperDP 𝗜𝚺₁` is `InstanceB2.lean`'s.
-/

namespace Cleanroom.Bli.BliLinkage.AttemptA

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliTrajectory

open Classical

namespace Abstract

/-! ## The empty process -/

/-- The deductive process with empty stages: every world is consistent with every stage.
Source: mandate § K2 ("an abstract `DP` whose stages decide nothing about the literals")
Kind: D
Fidelity: n/a -/
def emptyDP : DeductiveProcess := ⟨fun _ => ∅, fun _ => Finset.Subset.refl _⟩

/-- Every world is consistent with every stage of `emptyDP`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma consistentWith_emptyDP (v : PCWorld) (n : ℕ) : v.ConsistentWith (emptyDP.D n) :=
  fun _ h => by simp [emptyDP] at h

/-- Every world is consistent with the completed theory of `emptyDP`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma consistentWithTheory_emptyDP (v : PCWorld) : v.ConsistentWithTheory emptyDP :=
  fun n => consistentWith_emptyDP v n

/-! ## The Boolean cell family -/

/-- The literal atom index of day `m`, coordinate `c`: `⟨m, c⟩ + 1` (never `0`, the coordinate
atom's index; injective in `(m, c)`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def litCode (m c : ℕ) : ℕ := Nat.pair m c + 1

/-- `litCode_ne_zero`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma litCode_ne_zero (m c : ℕ) : litCode m c ≠ 0 := by unfold litCode; omega

/-- The two-cell Boolean literal: cell `0` is the atom, cell `1` its negation, any other index
is `⊥`.
Source: mandate § K2 (the witnesses' family, `d = 2` cells)
Kind: D
Fidelity: n/a -/
def boolLit (m c r : ℕ) : Sentence :=
  if r = 0 then Formula.atom (litCode m c) else if r = 1 then ∼ Formula.atom (litCode m c) else ⊥

/-- Exclusivity of the Boolean literals, in every world.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma boolLit_excl (m c r r' : ℕ) (hne : r ≠ r') (v : PCWorld) :
    ¬ (v.Holds (boolLit m c r) ∧ v.Holds (boolLit m c r')) := by
  rintro ⟨h1, h2⟩
  unfold boolLit at h1 h2
  split_ifs at h1 h2 with hr0 hr'0 hr'1 hr1 hr'0' hr'1'
  all_goals first
    | exact hne (by omega)
    | exact (PCWorld.holds_neg v _).1 h2 h1
    | exact (PCWorld.holds_neg v _).1 h1 h2
    | exact h1
    | exact h2

/-- Exhaustiveness of the Boolean literals, in every world.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma boolLit_exh (m c : ℕ) (v : PCWorld) :
    ∃ r ∈ ({0, 1} : Finset ℕ), v.Holds (boolLit m c r) := by
  by_cases h : v.Holds (Formula.atom (litCode m c))
  · exact ⟨0, by simp, by simpa [boolLit] using h⟩
  · exact ⟨1, by simp, by simpa [boolLit] using h⟩

/-- **The Boolean cell family** over any process, with representatives `ρ₀`, `ρ₁`: exclusivity
and exhaustiveness are Boolean facts about an atom and its negation.
Source: mandate § K2 (the witnesses' family)
Kind: D
Fidelity: n/a -/
def boolFamily (DP : DeductiveProcess) (ρ₀ ρ₁ : ℚ) : CellFamily DP where
  cellLit := boolLit
  cells _ := {0, 1}
  rep _ r := if r = 0 then ρ₀ else ρ₁
  excl := fun m c r r' hne v _ => boolLit_excl m c r r' hne v
  exh := fun m c v _ => boolLit_exh m c v

/-- Every world respects every day's partition of the Boolean family.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma boolFamily_partitions (DP : DeductiveProcess) (ρ₀ ρ₁ : ℚ) (m : ℕ) (v : PCWorld) :
    (boolFamily DP ρ₀ ρ₁).Partitions m v :=
  fun c => ⟨boolLit_exh m c v, fun r r' hne => boolLit_excl m c r r' hne v⟩

/-! ## The coordinate, the index, the two tables, the system -/

/-- The coordinate of record: the code of `bli-trajectory`'s `cohAtom = #0` (`= 3`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def c₀ : ℕ := Encodable.encode cohAtom

/-- `sentenceOfCode c₀ = cohAtom`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma sentenceOfCode_c₀ : sentenceOfCode c₀ = cohAtom := by simp [c₀]

/-- `c₀ = 3`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma c₀_eq : c₀ = 3 := by decide

/-- The index: the one coordinate `c₀` on every day.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def idx : ℕ → List ℕ := fun _ => [c₀]

/-- The table placing `c₀` in cell `0`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def tbl0 : ℕ := Encodable.encode [(c₀, 0)]

/-- The table placing `c₀` in cell `1`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def tbl1 : ℕ := Encodable.encode [(c₀, 1)]

/-- `tbl0 ≠ tbl1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tbl0_ne_tbl1 : tbl0 ≠ tbl1 := by
  intro h
  have := Encodable.encode_inj.1 h
  simp at this

/-- The candidate states: the two tables, every day.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def absStates : ℕ → Finset ℕ := fun _ => {tbl0, tbl1}

/-- The representative of a cell.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def repOf (ρ₀ ρ₁ : ℚ) (r : ℕ) : ℚ := if r = 0 then ρ₀ else ρ₁

/-- **The abstract state system**: states `absStates`, value at a sentence the representative of
its listed cell (`0` unlisted — `b2StateSystem`'s shape), realized state `tbl0`.
Source: mandate § K2 (the witnesses' system; `b2StateSystem`'s shape)
Kind: D
Fidelity: n/a -/
noncomputable def absSystem (ρ₀ ρ₁ : ℚ) : StateSystem where
  states := absStates
  val _ q φ := (((entryOf (Encodable.encode φ) (tableOfCode q)).map (repOf ρ₀ ρ₁)).getD 0 : ℚ)
  actual _ := tbl0
  actual_mem _ := by simp [absStates]

/-- The abstract system is `Tabular` over the Boolean family.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem absSystem_tabular (DP : DeductiveProcess) (ρ₀ ρ₁ : ℚ) :
    Tabular (boolFamily DP ρ₀ ρ₁) idx (absSystem ρ₀ ρ₁) where
  keys := by
    intro m q hq c hc
    simp only [absSystem, absStates, Finset.mem_insert, Finset.mem_singleton] at hq
    simp only [idx, List.mem_singleton] at hc
    subst hc
    rcases hq with rfl | rfl
    · exact ⟨0, by simp [boolFamily], by unfold tbl0; rw [tableOfCode_encode]; simp [entryOf]⟩
    · exact ⟨1, by simp [boolFamily], by unfold tbl1; rw [tableOfCode_encode]; simp [entryOf]⟩
  val := by
    intro m q hq c hc r he
    simp only [idx, List.mem_singleton] at hc
    subst hc
    simp only [absSystem, sentenceOfCode_c₀, boolFamily]
    rw [show Encodable.encode cohAtom = c₀ from rfl, he]
    simp [repOf]
  genuine := by
    intro m c hc
    simp only [idx, List.mem_singleton] at hc
    subst hc
    simp [c₀]

/-- The linked state sentence of `tbl0`: the literal atom and `⊤`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateOf_tbl0 (DP : DeductiveProcess) (ρ₀ ρ₁ : ℚ) (m : ℕ) :
    stateOf (boolFamily DP ρ₀ ρ₁) m tbl0 = (Formula.atom (litCode m c₀) ⋏ ⊤) := by
  unfold stateOf tbl0
  rw [tableOfCode_encode]
  simp [boolFamily, boolLit, conjList]

/-- The linked state sentence of `tbl1`: the negated literal atom and `⊤`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateOf_tbl1 (DP : DeductiveProcess) (ρ₀ ρ₁ : ℚ) (m : ℕ) :
    stateOf (boolFamily DP ρ₀ ρ₁) m tbl1 = (∼ Formula.atom (litCode m c₀) ⋏ ⊤) := by
  unfold stateOf tbl1
  rw [tableOfCode_encode]
  simp [boolFamily, boolLit, conjList]

/-! ## The four worlds and their mixtures -/

/-- Every atom true.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def wAll : PCWorld := fun _ => True

/-- Every literal atom true, the coordinate atom `#0` false.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def wLit : PCWorld := fun a => a ≠ 0

/-- Only the coordinate atom `#0` true.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def wCoh : PCWorld := fun a => a = 0

/-- Every atom false.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def wNone : PCWorld := fun _ => False

/-- The four worlds as a `Fin 4`-family.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def worlds : Fin 4 → PCWorld := ![wAll, wLit, wCoh, wNone]

/-- **The mixture history** with weights `a, b, c, d` on `wAll, wLit, wCoh, wNone`, the same on
every day.
Source: mandate § K2 (the witnesses as explicit world mixtures)
Kind: D
Fidelity: n/a -/
noncomputable def mix4 (a b c d : ℝ) : History :=
  fun _ φ => a * wAll.payout φ + b * wLit.payout φ + c * wCoh.payout φ + d * wNone.payout φ

/-- A nonnegative unit-mass `mix4` is `CoherentOnCell` over `emptyDP` on every algebra, every
partition day and every day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mix4_coherentOnCell (ρ₀ ρ₁ : ℚ) {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hsum : a + b + c + d = 1) (k m : ℕ) (A : Finset ℕ) (n : ℕ) :
    CoherentOnCell (boolFamily emptyDP ρ₀ ρ₁) (emptyDP.D k) m A (mix4 a b c d n) := by
  refine ⟨4, worlds, ![a, b, c, d],
    fun i => ⟨consistentWith_emptyDP _ _, boolFamily_partitions _ _ _ _ _⟩,
    fun i => ?_, ?_, fun φ _ => ?_⟩
  · fin_cases i <;> simp [ha, hb, hc, hd]
  · simp [Fin.sum_univ_four]; linarith
  · simp [mix4, worlds, Fin.sum_univ_four]

/-- `mix4` satisfies `PCPσ` over the abstract system.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mix4_PCPσ (ρ₀ ρ₁ : ℚ) {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hsum : a + b + c + d = 1) :
    PCPσ (boolFamily emptyDP ρ₀ ρ₁) (stateOf (boolFamily emptyDP ρ₀ ρ₁)) (absSystem ρ₀ ρ₁)
      (mix4 a b c d) :=
  fun n => mix4_coherentOnCell ρ₀ ρ₁ ha hb hc hd hsum n (n + 1) _ n

/-! ## The values of the mixtures on the sentences the predicates read -/

/-- The payouts of the four worlds on the literal atom of day `m`: `1, 1, 0, 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_lit (m : ℕ) :
    wAll.payout (Formula.atom (litCode m c₀)) = 1 ∧ wLit.payout (Formula.atom (litCode m c₀)) = 1 ∧
      wCoh.payout (Formula.atom (litCode m c₀)) = 0 ∧ wNone.payout (Formula.atom (litCode m c₀)) = 0 := by
  simp [PCWorld.payout, wAll, wLit, wCoh, wNone, litCode_ne_zero]

/-- The payouts on the coordinate atom `cohAtom`: `1, 0, 1, 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_coh :
    wAll.payout cohAtom = 1 ∧ wLit.payout cohAtom = 0 ∧ wCoh.payout cohAtom = 1 ∧
      wNone.payout cohAtom = 0 := by
  simp [PCWorld.payout, wAll, wLit, wCoh, wNone, cohAtom]

/-- A world's payout of `φ ⋏ ⊤` is its payout of `φ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_and_top (v : PCWorld) (φ : Sentence) : v.payout (φ ⋏ ⊤) = v.payout φ := by
  rw [payout_and, payout_top, mul_one]

/-- A world's payouts of `φ` and `∼φ` sum to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_add_payout_neg (v : PCWorld) (φ : Sentence) : v.payout φ + v.payout (∼φ) = 1 := by
  unfold PCWorld.payout
  by_cases h : v.Holds φ <;> simp [h]

/-- `mix4` on the state sentence of `tbl0`: `a + b`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mix4_state0 {ρ₀ ρ₁ : ℚ} (a b c d : ℝ) (n m : ℕ) :
    mix4 a b c d n (stateOf (boolFamily emptyDP ρ₀ ρ₁) m tbl0) = a + b := by
  obtain ⟨h1, h2, h3, h4⟩ := payout_lit m
  simp only [mix4, stateOf_tbl0, payout_and_top, h1, h2, h3, h4]; ring

/-- `mix4` on the state sentence of `tbl1`: `c + d`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mix4_state1 {ρ₀ ρ₁ : ℚ} (a b c d : ℝ) (n m : ℕ) :
    mix4 a b c d n (stateOf (boolFamily emptyDP ρ₀ ρ₁) m tbl1) = c + d := by
  obtain ⟨h1, h2, h3, h4⟩ := payout_lit m
  have e1 := payout_add_payout_neg wAll (Formula.atom (litCode m c₀))
  have e2 := payout_add_payout_neg wLit (Formula.atom (litCode m c₀))
  have e3 := payout_add_payout_neg wCoh (Formula.atom (litCode m c₀))
  have e4 := payout_add_payout_neg wNone (Formula.atom (litCode m c₀))
  simp only [mix4, stateOf_tbl1, payout_and_top]
  rw [h1] at e1; rw [h2] at e2; rw [h3] at e3; rw [h4] at e4
  linear_combination b * e2 + a * e1 + c * e3 + d * e4

/-- `mix4` on the two state sentences conjoined: `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mix4_state01 {ρ₀ ρ₁ : ℚ} (a b c d : ℝ) (n m : ℕ) :
    mix4 a b c d n
      (stateOf (boolFamily emptyDP ρ₀ ρ₁) m tbl0 ⋏ stateOf (boolFamily emptyDP ρ₀ ρ₁) m tbl1) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := payout_lit m
  have e1 := payout_add_payout_neg wAll (Formula.atom (litCode m c₀))
  have e2 := payout_add_payout_neg wLit (Formula.atom (litCode m c₀))
  have e3 := payout_add_payout_neg wCoh (Formula.atom (litCode m c₀))
  have e4 := payout_add_payout_neg wNone (Formula.atom (litCode m c₀))
  simp only [mix4, stateOf_tbl0, stateOf_tbl1, payout_and, payout_top, mul_one]
  rw [h1] at e1 ⊢; rw [h2] at e2 ⊢; rw [h3] at e3 ⊢; rw [h4] at e4 ⊢
  linear_combination a * e1 + b * e2

/-- `mix4` on the coordinate atom: `a + c`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mix4_coh (a b c d : ℝ) (n : ℕ) : mix4 a b c d n cohAtom = a + c := by
  obtain ⟨h1, h2, h3, h4⟩ := payout_coh
  simp only [mix4, h1, h2, h3, h4]; ring

/-- `mix4` on the coordinate conjoined with the state of `tbl0`: `a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mix4_coh_state0 {ρ₀ ρ₁ : ℚ} (a b c d : ℝ) (n m : ℕ) :
    mix4 a b c d n (cohAtom ⋏ stateOf (boolFamily emptyDP ρ₀ ρ₁) m tbl0) = a := by
  obtain ⟨h1, h2, h3, h4⟩ := payout_lit m
  obtain ⟨g1, g2, g3, g4⟩ := payout_coh
  simp only [mix4, stateOf_tbl0, payout_and, payout_top, mul_one, h1, h2, h3, h4, g1, g2, g3, g4]
  ring

/-- `mix4` on the coordinate conjoined with the state of `tbl1`: `c`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mix4_coh_state1 {ρ₀ ρ₁ : ℚ} (a b c d : ℝ) (n m : ℕ) :
    mix4 a b c d n (cohAtom ⋏ stateOf (boolFamily emptyDP ρ₀ ρ₁) m tbl1) = c := by
  obtain ⟨h1, h2, h3, h4⟩ := payout_lit m
  obtain ⟨g1, g2, g3, g4⟩ := payout_coh
  have e1 := payout_add_payout_neg wAll (Formula.atom (litCode m c₀))
  have e2 := payout_add_payout_neg wLit (Formula.atom (litCode m c₀))
  have e3 := payout_add_payout_neg wCoh (Formula.atom (litCode m c₀))
  have e4 := payout_add_payout_neg wNone (Formula.atom (litCode m c₀))
  simp only [mix4, stateOf_tbl1, payout_and, payout_top, mul_one, g1, g2, g3, g4]
  rw [h1] at e1; rw [h2] at e2; rw [h3] at e3; rw [h4] at e4
  linear_combination a * e1 + c * e3

/-- `mix4` on the positive literal `boolLit m c₀ 0`: `a + b`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mix4_lit0 (a b c d : ℝ) (n m : ℕ) : mix4 a b c d n (boolLit m c₀ 0) = a + b := by
  obtain ⟨h1, h2, h3, h4⟩ := payout_lit m
  simp only [mix4, boolLit, if_true, h1, h2, h3, h4]; ring

/-- `mix4` on the negative literal `boolLit m c₀ 1`: `c + d`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mix4_lit1 (a b c d : ℝ) (n m : ℕ) : mix4 a b c d n (boolLit m c₀ 1) = c + d := by
  obtain ⟨h1, h2, h3, h4⟩ := payout_lit m
  have e1 := payout_add_payout_neg wAll (Formula.atom (litCode m c₀))
  have e2 := payout_add_payout_neg wLit (Formula.atom (litCode m c₀))
  have e3 := payout_add_payout_neg wCoh (Formula.atom (litCode m c₀))
  have e4 := payout_add_payout_neg wNone (Formula.atom (litCode m c₀))
  simp only [mix4, boolLit, if_true, one_ne_zero, if_false]
  rw [h1] at e1; rw [h2] at e2; rw [h3] at e3; rw [h4] at e4
  linear_combination a * e1 + b * e2 + c * e3 + d * e4

/-- `mix4` of a conjunction is symmetric.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mix4_and_comm (a b c d : ℝ) (n : ℕ) (φ ψ : Sentence) :
    mix4 a b c d n (φ ⋏ ψ) = mix4 a b c d n (ψ ⋏ φ) := by
  simp only [mix4, payout_and]; ring

/-! ## The predicates on `mix4` -/

/-- `mix4` satisfies `E5σ` over the abstract system whenever its weights sum to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mix4_E5σ (ρ₀ ρ₁ : ℚ) {a b c d : ℝ} (hsum : a + b + c + d = 1) :
    E5σ (stateOf (boolFamily emptyDP ρ₀ ρ₁)) (absSystem ρ₀ ρ₁) (mix4 a b c d) := by
  intro n
  refine ⟨?_, ?_⟩
  · show ∑ q ∈ ({tbl0, tbl1} : Finset ℕ), _ = 1
    rw [Finset.sum_pair tbl0_ne_tbl1, mix4_state0, mix4_state1]; linarith
  · intro q₁ hq₁ q₂ hq₂ hne
    simp only [absSystem, absStates, Finset.mem_insert, Finset.mem_singleton] at hq₁ hq₂
    rcases hq₁ with rfl | rfl <;> rcases hq₂ with rfl | rfl
    · exact absurd rfl hne
    · exact mix4_state01 a b c d n (n + 1)
    · rw [mix4_and_comm]
      exact mix4_state01 a b c d n (n + 1)
    · exact absurd rfl hne

/-- The abstract system's value of `cohAtom` at `tbl0` is `ρ₀`, at `tbl1` is `ρ₁`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma absSystem_val_coh (ρ₀ ρ₁ : ℚ) (m : ℕ) :
    (absSystem ρ₀ ρ₁).val m tbl0 cohAtom = ρ₀ ∧ (absSystem ρ₀ ρ₁).val m tbl1 cohAtom = ρ₁ := by
  constructor
  · simp only [absSystem]; unfold tbl0
    rw [show Encodable.encode cohAtom = c₀ from rfl, tableOfCode_encode]; simp [entryOf, repOf]
  · simp only [absSystem]; unfold tbl1
    rw [show Encodable.encode cohAtom = c₀ from rfl, tableOfCode_encode]; simp [entryOf, repOf]

/-- **`mix4` with faithful weights satisfies faith on the index**: with masses `m₀`, `m₁` on the
two tables and the coordinate true inside each in proportion `ρ₀`, `ρ₁`, constraint 2 holds at
`c₀` toward every future day.
Source: mandate § K2 (T3: "the K5 product coupling … extended to a world mixture")
Kind: L
Fidelity: n/a -/
theorem mix4_E2xσIdx (ρ₀ ρ₁ : ℚ) (m₀ m₁ : ℝ) :
    E2xσIdx (stateOf (boolFamily emptyDP ρ₀ ρ₁)) idx (absSystem ρ₀ ρ₁)
      (mix4 (m₀ * ρ₀) (m₀ * (1 - ρ₀)) (m₁ * ρ₁) (m₁ * (1 - ρ₁))) := by
  intro n m _ q hq c hc _
  simp only [idx, List.mem_singleton] at hc
  subst hc
  simp only [absSystem, absStates, Finset.mem_insert, Finset.mem_singleton] at hq
  rw [sentenceOfCode_c₀]
  obtain ⟨hv0, hv1⟩ := absSystem_val_coh ρ₀ ρ₁ m
  rcases hq with rfl | rfl
  · rw [mix4_coh_state0, mix4_state0, hv0]; ring
  · rw [mix4_coh_state1, mix4_state1, hv1]; ring

/-- The literal atom index of day `3` at `c₀` is `16`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma litCode_three : litCode 3 c₀ = 16 := by rw [c₀_eq]; decide

/-- `sizeBound 2 = 16`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sizeBound_two : sizeBound 2 = 16 := by norm_num [sizeBound]

/-- Both day-`3` literals of `c₀` are small on day `2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma smallOn_two_lit : SmallOn 2 (boolLit 3 c₀ 0) ∧ SmallOn 2 (boolLit 3 c₀ 1) := by
  have hd : (natDigits4 (16 + 5)).length ≤ 3 := length_natDigits4_le_of_lt_pow (by norm_num)
  constructor
  · unfold SmallOn boolLit
    simp only [if_true]
    rw [tokenSize_atom, litCode_three, sizeBound_two]; omega
  · unfold SmallOn boolLit
    simp only [one_ne_zero, if_false, if_true]
    rw [tokenSize_neg, tokenSize_atom, litCode_three, sizeBound_two]; omega

/-- **`c₀` is pinned on day `2`** (the witness day).
Source: mandate § K2 ("pinned set non-empty" at the witness)
Kind: L
Fidelity: n/a -/
lemma c₀_mem_pinned_two (DP : DeductiveProcess) (ρ₀ ρ₁ : ℚ) :
    c₀ ∈ pinned (boolFamily DP ρ₀ ρ₁) idx 2 := by
  rw [mem_pinned]
  refine ⟨by simp [idx], fun r hr => ?_⟩
  simp only [boolFamily, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl
  · exact smallOn_two_lit.1
  · exact smallOn_two_lit.2

/-- A pinned day is `≥ 1` (an atom has size `≥ 3 > sizeBound 0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma one_le_of_mem_pinned (DP : DeductiveProcess) (ρ₀ ρ₁ : ℚ) {n c : ℕ}
    (h : c ∈ pinned (boolFamily DP ρ₀ ρ₁) idx n) : 1 ≤ n := by
  rw [mem_pinned] at h
  have h0 := h.2 0 (by simp [boolFamily])
  unfold SmallOn at h0
  simp only [boolFamily, boolLit, if_true] at h0
  have h3 := three_le_tokenSize_atom (litCode (n + 1) c)
  by_contra hn
  rw [not_le] at hn
  interval_cases n
  have : sizeBound 0 = 2 := by norm_num [sizeBound]
  omega

/-- Nothing is pinned on day `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma not_mem_pinned_zero (DP : DeductiveProcess) (ρ₀ ρ₁ : ℚ) (c : ℕ) :
    c ∉ pinned (boolFamily DP ρ₀ ρ₁) idx 0 :=
  fun h => by have := one_le_of_mem_pinned DP ρ₀ ρ₁ h; omega

/-- **The scope condition of `determination` holds for the abstract index**: a pinned coordinate
is `c₀`, whose sentence `cohAtom` is small from day `1` and in `Sminus m m` for every `m ≥ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem scope_idx (DP : DeductiveProcess) (ρ₀ ρ₁ : ℚ) :
    ∀ n, ∀ c ∈ pinned (boolFamily DP ρ₀ ρ₁) idx n,
      sentenceOfCode c ∈ smallSet n ∧ sentenceOfCode c ∈ Sminus (n + 1) (n + 1) := by
  intro n c hc
  have hn := one_le_of_mem_pinned DP ρ₀ ρ₁ hc
  have hc' : c = c₀ := by simpa [idx] using (mem_pinned.1 hc).1
  subst hc'
  rw [sentenceOfCode_c₀]
  exact ⟨mem_smallSet.mpr (cohAtom_smallOn hn), cohAtom_mem_Sminus (by omega)⟩

/-- **`D_NNUcell` at `(n, c₀)` for a `mix4`, in closed form**: the identity
`a + c = ρ₀ (a + b) + ρ₁ (c + d)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma nnu_mix4_iff (ρ₀ ρ₁ : ℚ) (a b c d : ℝ) (n : ℕ) :
    (mix4 a b c d n (sentenceOfCode c₀) =
      ∑ r ∈ (boolFamily emptyDP ρ₀ ρ₁).cells (n + 1),
        ((boolFamily emptyDP ρ₀ ρ₁).rep (n + 1) r : ℝ) *
          mix4 a b c d n ((boolFamily emptyDP ρ₀ ρ₁).cellLit (n + 1) c₀ r)) ↔
    a + c = ρ₀ * (a + b) + ρ₁ * (c + d) := by
  simp only [boolFamily, sentenceOfCode_c₀, mix4_coh]
  rw [Finset.sum_pair (by decide : (0 : ℕ) ≠ 1), mix4_lit0, mix4_lit1]
  simp

end Abstract

end Cleanroom.Bli.BliLinkage.AttemptA
