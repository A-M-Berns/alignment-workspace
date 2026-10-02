import Cleanroom.Bli.BliLinkageB.Determination
import Cleanroom.Bli.BliLinkageB.Faith
import LogicalInduction.Framework.Machine.SentenceMachine

/-!
# bli-linkage, angle B — the B2 instances at `𝗜𝚺₁`, `halfRound`, `fixedStates`

The construction-facing module: the abstract objects of `Defs.lean` instantiated at
`bli-found`'s B2 encoding over FAF's `paperDP T`.

* `intervalFamilyB2 T`: the quote family `quoteAt T` with its price `paperQuote`, the two
  reflection fields being `holds_quoteAt_of_lt_of_lt` and `le_of_holds_quoteAt`.
* `cellFamilyB2 T round hround cells hcells rep`: the cell literals `cellSentence`, exclusive and
  exhaustive in every completed-theory world by `cellSentence_reflected` and the rounding being
  total into `cells`. Its `stateOf` is the B2 `stateSentence` on every table listing genuine
  sentence codes (`stateOf_cellFamilyB2_eq`), in particular on `Grid.fixedStates`.
* The four-table grid `fixedStates` over `[⌜⊥⌝, ⌜⊤⌝]` has the two grid properties the
  stage-level determination theorem needs — `SpuriousEntails` (`fixedStates_spuriousEntails`)
  and `ValuesAtRep` (`fixedSystem_valuesAtRep`) — and its index lists codes.
* **The pinned set is eventually non-empty** (`pinned_eventually_B2`): both coordinates'
  cell literals are machine-metered families (atoms over a `Nat.pair`-nest of the day), hence
  day-small from some day on (`bli-found`'s `machineSentenceCodes_eventually_small`). `∃ N`
  is what is provable; the quote code's constant is opaque, so no numeral is promised.
* **The headline instance** `d_nnucell_B2`: over `paperDP 𝗜𝚺₁`, any superbelief `P` satisfying
  `PCPσ ∧ E5σ ∧ E1x Q P ∧ E2xσ` at the B2 state sentence on the fixed grid forces
  `D_NNUcell` on the base `Q` — for every `Q` (FAF's LIA included), at the stage level.
-/

namespace Cleanroom.Bli.BliLinkageB

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

section Generic

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]

/-- **The B2 interval family**: `quoteAt T` about the price `paperQuote T m ⌜φ⌝`.
Source: mandate § Definitions (angle B: `IntervalFamily`); bli-found T7
Kind: D
Fidelity: exact -/
noncomputable def intervalFamilyB2 : IntervalFamily (paperDP T) where
  quote := quoteAt T
  price m φ := paperQuote T m (Encodable.encode φ)
  reflect_lt _ _ _ _ h1 h2 v hv := holds_quoteAt_of_lt_of_lt T h1 h2 v hv
  le_of_holds _ _ _ _ v hv h := le_of_holds_quoteAt T v hv h

/-- **The B2 cell family**: literals `cellSentence T round hround m ⌜φ⌝ r`; exclusivity and
exhaustiveness in every completed-theory world from `cellSentence_reflected` and the rounding's
totality into `cells`.
Source: mandate § Definitions (`CellFamily`, B2 instance); bli-found T7
Kind: D
Fidelity: exact -/
noncomputable def cellFamilyB2 (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (cells : ℕ → Finset ℕ)
    (hcells : ∀ m x, round m x ∈ cells m) (rep : ℕ → ℕ → ℚ) : CellFamilyT (paperDP T) where
  literal m φ r := cellSentence T round hround m (Encodable.encode φ) r
  cells := cells
  rep := rep
  excl := by
    intro m φ r r' hne v hv ⟨h, h'⟩
    rw [cellSentence_reflected T round hround m _ r v hv] at h
    rw [cellSentence_reflected T round hround m _ r' v hv] at h'
    exact hne (h.symm.trans h')
  exh := by
    intro m φ v hv
    exact ⟨_, hcells m _, (cellSentence_reflected T round hround m _ _ v hv).2 rfl⟩

/-- The B2 cell family's literal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma cellFamilyB2_literal (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (cells : ℕ → Finset ℕ)
    (hcells : ∀ m x, round m x ∈ cells m) (rep : ℕ → ℕ → ℚ) (m : ℕ) (φ : Sentence) (r : ℕ) :
    (cellFamilyB2 T round hround cells hcells rep).literal m φ r =
      cellSentence T round hround m (Encodable.encode φ) r := rfl

/-- The B2 cell family's cells and representatives.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma cellFamilyB2_cells (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (cells : ℕ → Finset ℕ)
    (hcells : ∀ m x, round m x ∈ cells m) (rep : ℕ → ℕ → ℚ) :
    (cellFamilyB2 T round hround cells hcells rep).cells = cells ∧
      (cellFamilyB2 T round hround cells hcells rep).rep = rep := ⟨rfl, rfl⟩

/-- **`stateOf` is the B2 state sentence** on every table whose keys are genuine sentence codes
(the mandate's `stateOf_eq_stateSentence`; not `rfl` in general because `stateOf`'s literal takes
the *sentence* and `cellSentence` the *code*, which agree exactly on genuine codes).
Source: mandate § Definitions (`stateOf_eq_stateSentence`)
Kind: L
Fidelity: exact (on tables listing genuine codes) -/
theorem stateOf_cellFamilyB2_eq (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (cells : ℕ → Finset ℕ)
    (hcells : ∀ m x, round m x ∈ cells m) (rep : ℕ → ℕ → ℚ) (m q : ℕ)
    (hq : ∀ e ∈ tableOfCode q, Encodable.encode (sentenceOfCode e.1) = e.1) :
    stateOf (cellFamilyB2 T round hround cells hcells rep) m q = stateSentence T round hround m q := by
  unfold stateOf stateSentence
  congr 1
  exact List.map_congr_left fun e he => by rw [cellFamilyB2_literal, hq e he]

end Generic

/-! ## Transport along a state-family equality on the candidates -/

section Transport

variable {σ σ' : ℕ → ℕ → Sentence} {S : StateSystem} {P : History}

/-- `E5σ` depends on `σ` only on the candidates.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E5σ_congr (h : ∀ m, ∀ q ∈ S.states m, σ m q = σ' m q) : E5σ σ S P ↔ E5σ σ' S P := by
  constructor <;> intro H n <;> obtain ⟨h1, h2⟩ := H n <;> refine ⟨?_, ?_⟩
  · rw [← h1]; exact Finset.sum_congr rfl fun q hq => by rw [h _ q hq]
  · intro q₁ hq₁ q₂ hq₂ hne; rw [← h _ q₁ hq₁, ← h _ q₂ hq₂]; exact h2 q₁ hq₁ q₂ hq₂ hne
  · rw [← h1]; exact Finset.sum_congr rfl fun q hq => by rw [h _ q hq]
  · intro q₁ hq₁ q₂ hq₂ hne; rw [h _ q₁ hq₁, h _ q₂ hq₂]; exact h2 q₁ hq₁ q₂ hq₂ hne

/-- `E2xσ` depends on `σ` only on the candidates.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E2xσ_congr (h : ∀ m, ∀ q ∈ S.states m, σ m q = σ' m q) : E2xσ σ S P ↔ E2xσ σ' S P := by
  constructor <;> intro H n m hnm q hq φ hφ
  · rw [← h m q hq]; exact H n m hnm q hq φ hφ
  · rw [h m q hq]; exact H n m hnm q hq φ hφ

/-- `stateAtoms` depends on `σ` only on the candidates.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem stateAtoms_congr (h : ∀ m, ∀ q ∈ S.states m, σ m q = σ' m q) (n : ℕ) :
    stateAtoms σ S n = stateAtoms σ' S n :=
  Finset.biUnion_congr rfl fun q hq => by rw [h _ q hq]

end Transport

/-! ## The fixed grid at `𝗜𝚺₁` -/

/-- The two-cell grid `{0, 1}` on every day.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def twoCells (_m : ℕ) : Finset ℕ := {0, 1}

/-- `halfRound` is total into `twoCells`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma halfRound_mem_twoCells (m : ℕ) (x : ℚ) : halfRound m x ∈ twoCells m := by
  have := halfRound_le_one m x
  simp only [twoCells, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- **The cell family of record at `𝗜𝚺₁`**: `halfRound`, cells `{0, 1}`, representatives `rep`
(a parameter: `bli-found`'s `witnessRep` makes the package unsatisfiable,
`fixedSystem_witnessRep_unsat`).
Source: mandate § Definitions (B2 instance); bli-found T7 (witness)
Kind: D
Fidelity: n/a -/
noncomputable def fixedCF (rep : ℕ → ℕ → ℚ) : CellFamilyT (paperDP 𝗜𝚺₁) :=
  cellFamilyB2 𝗜𝚺₁ halfRound halfRound_computable twoCells halfRound_mem_twoCells rep

/-- **The fixed grid as a B2 system with representatives `rep`** (`bli-found`'s `fixedSystem` is
the instance `rep := witnessRep`, definitionally).
Source: bli-found `Grid.fixedSystem`
Kind: D
Fidelity: n/a -/
noncomputable def fixedSystemR (rep : ℕ → ℕ → ℚ) : StateSystem :=
  b2StateSystem 𝗜𝚺₁ halfRound witnessIndex fixedStates actualCode_mem_fixedStates rep

/-- `fixedSystem = fixedSystemR witnessRep`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fixedSystem_eq : fixedSystem = fixedSystemR witnessRep := rfl

/-- The B2 state sentence of record at `𝗜𝚺₁`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable abbrev σB2 : ℕ → ℕ → Sentence := stateSentence 𝗜𝚺₁ halfRound halfRound_computable

/-- Membership in the fixed grid: the four tables over `[⌜⊥⌝, ⌜⊤⌝]` with indices `≤ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_fixedStates_iff {m q : ℕ} :
    q ∈ fixedStates m ↔ ∃ a b, a ≤ 1 ∧ b ≤ 1 ∧ q = Encodable.encode (tbl a b) := by
  simp only [fixedStates, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, le_rfl.trans zero_le_one, zero_le_one, rfl⟩
    · exact ⟨0, 1, zero_le_one, le_rfl, rfl⟩
    · exact ⟨1, 0, le_rfl, zero_le_one, rfl⟩
    · exact ⟨1, 1, le_rfl, le_rfl, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> simp

/-- The codes of `⊥` and `⊤` differ.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma encode_falsum_ne_encode_verum :
    Encodable.encode (⊥ : Sentence) ≠ Encodable.encode (⊤ : Sentence) := by
  simp

/-- The entry of a fixed table at `⌜⊥⌝`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma entryOf_tbl_bot (a b : ℕ) : entryOf (Encodable.encode (⊥ : Sentence)) (tbl a b) = some a := by
  simp [tbl, entryOf]

/-- The entry of a fixed table at `⌜⊤⌝`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma entryOf_tbl_top (a b : ℕ) : entryOf (Encodable.encode (⊤ : Sentence)) (tbl a b) = some b := by
  simp [tbl, entryOf]

/-- `fixedSystem.states`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma fixedSystemR_states (rep : ℕ → ℕ → ℚ) : (fixedSystemR rep).states = fixedStates := rfl

/-- Membership in the witness index.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_witnessIndex_iff {m c : ℕ} :
    c ∈ witnessIndex m ↔
      c = Encodable.encode (⊥ : Sentence) ∨ c = Encodable.encode (⊤ : Sentence) := by
  simp [witnessIndex]

/-- The witness index lists codes.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem witnessIndex_codes (m : ℕ) : IndexCodes witnessIndex m := by
  intro c hc
  rcases mem_witnessIndex_iff.1 hc with rfl | rfl <;> simp

/-- A world holds `stateOf fixedCF` of a fixed table iff it holds the two literals.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_stateOf_tbl (rep : ℕ → ℕ → ℚ) (m a b : ℕ) (v : PCWorld) :
    v.Holds (stateOf (fixedCF rep) m (Encodable.encode (tbl a b))) ↔
      v.Holds ((fixedCF rep).literal m ⊥ a) ∧ v.Holds ((fixedCF rep).literal m ⊤ b) := by
  rw [holds_stateOf, tableOfCode_encode]
  simp [tbl]

/-- **The fixed grid has `SpuriousEntails`**: a fixed table together with a literal it does not
list at one of the two coordinates entails the table with that coordinate's index replaced.
Source: this package (`Defs.SpuriousEntails`); bli-found `Grid.fixedStates`
Kind: L
Fidelity: n/a -/
theorem fixedStates_spuriousEntails (rep : ℕ → ℕ → ℚ) (n : ℕ) :
    SpuriousEntails (stateOf (fixedCF rep)) (fixedCF rep).literal (fixedSystemR rep) witnessIndex
      twoCells n := by
  intro q hq c hc r hr hne
  rw [fixedSystemR_states] at hq
  obtain ⟨a, b, ha, hb, rfl⟩ := (mem_fixedStates_iff (m := n + 1)).1 hq
  have hr1 : r ≤ 1 := by
    simp only [twoCells, Finset.mem_insert, Finset.mem_singleton] at hr; omega
  rw [tableOfCode_encode] at hne
  rcases mem_witnessIndex_iff.1 hc with rfl | rfl
  · rw [entryOf_tbl_bot] at hne
    have har : a ≠ r := fun h => hne (by rw [h])
    refine ⟨Encodable.encode (tbl r b),
      (mem_fixedStates_iff (m := n + 1)).2 ⟨r, b, hr1, hb, rfl⟩, ?_, ?_⟩
    · intro h; rw [Encodable.encode_inj, tbl_inj] at h; exact har h.1.symm
    · intro v hs hl
      rw [holds_stateOf_tbl] at hs ⊢
      exact ⟨by simpa using hl, hs.2⟩
  · rw [entryOf_tbl_top] at hne
    have hbr : b ≠ r := fun h => hne (by rw [h])
    refine ⟨Encodable.encode (tbl a r),
      (mem_fixedStates_iff (m := n + 1)).2 ⟨a, r, ha, hr1, rfl⟩, ?_, ?_⟩
    · intro h; rw [Encodable.encode_inj, tbl_inj] at h; exact hbr h.2.symm
    · intro v hs hl
      rw [holds_stateOf_tbl] at hs ⊢
      exact ⟨hs.1, by simpa using hl⟩

/-- **The fixed system values every coordinate at the representative of the cell it lists.**
Source: mandate K2 (`hval`, discharged at B2)
Kind: L
Fidelity: n/a -/
theorem fixedSystem_valuesAtRep (rep : ℕ → ℕ → ℚ) (n : ℕ) :
    ValuesAtRep (fixedCF rep) (fixedSystemR rep) witnessIndex n := by
  intro q hq c hc
  rw [fixedSystemR_states] at hq
  obtain ⟨a, b, ha, hb, rfl⟩ := (mem_fixedStates_iff (m := n + 1)).1 hq
  have ha' : a ∈ twoCells (n + 1) := by
    simp only [twoCells, Finset.mem_insert, Finset.mem_singleton]; omega
  have hb' : b ∈ twoCells (n + 1) := by
    simp only [twoCells, Finset.mem_insert, Finset.mem_singleton]; omega
  rcases mem_witnessIndex_iff.1 hc with rfl | rfl
  · refine ⟨a, ha', by rw [tableOfCode_encode, entryOf_tbl_bot], ?_⟩
    show ((((entryOf _ (tableOfCode _)).map (rep (n + 1))).getD 0 : ℚ) : ℝ) = _
    rw [sentenceOfCode_encode, tableOfCode_encode, entryOf_tbl_bot]
    rfl
  · refine ⟨b, hb', by rw [tableOfCode_encode, entryOf_tbl_top], ?_⟩
    show ((((entryOf _ (tableOfCode _)).map (rep (n + 1))).getD 0 : ℚ) : ℝ) = _
    rw [sentenceOfCode_encode, tableOfCode_encode, entryOf_tbl_top]
    rfl

/-- On the fixed grid, `stateOf fixedCF` is the B2 state sentence.
Source: mandate § Definitions (`stateOf_eq_stateSentence`)
Kind: L
Fidelity: n/a -/
theorem stateOf_fixedCF_eq (rep : ℕ → ℕ → ℚ) (m : ℕ) {q : ℕ} (hq : q ∈ fixedStates m) :
    stateOf (fixedCF rep) m q = σB2 m q := by
  obtain ⟨a, b, -, -, rfl⟩ := (mem_fixedStates_iff (m := m)).1 hq
  refine stateOf_cellFamilyB2_eq 𝗜𝚺₁ halfRound halfRound_computable twoCells
    halfRound_mem_twoCells rep m _ fun e he => ?_
  rw [tableOfCode_encode] at he
  simp only [tbl, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> simp

/-! ## The pinned set at `𝗜𝚺₁` is eventually non-empty -/

/-- A cell literal of a fixed sentence code is a machine-metered family in the day: the atom
index is a `Nat.pair`-nest of constants and the day.
Source: bli-leak `machineSentenceCodes_atom_of_machineDigits` (inlined); FAF `MachineDigits.natPair`
Kind: L
Fidelity: n/a -/
theorem cellSentence_machineSentenceCodes (c r : ℕ) :
    MachineSentenceCodes fun n => cellSentence 𝗜𝚺₁ halfRound halfRound_computable (n + 1) c r := by
  have hd : MachineDigits fun n => quotationClaimCode universalQuotePos universalQuoteNeg
      (Nat.pair (cellQuote 𝗜𝚺₁ halfRound halfRound_computable).code
        (Nat.pair (n + 1) (Nat.pair c r))) :=
    (MachineDigits.natPair (MachineDigits.const 2)
      (MachineDigits.natPair (MachineDigits.const (Encodable.encode universalQuotePos))
        (MachineDigits.natPair (MachineDigits.const (Encodable.encode universalQuoteNeg))
          (MachineDigits.natPair
            (MachineDigits.const (cellQuote 𝗜𝚺₁ halfRound halfRound_computable).code)
            (MachineDigits.natPair
              ((MachineDigits.ofUnaryRuler UnaryRuler.id).add (MachineDigits.const 1))
              (MachineDigits.const (Nat.pair c r))))))).of_eq (fun _ => rfl)
  exact MachineSentenceCodes.ofCanonical
    (MachineTokenStream.of_eq (hd.add (MachineDigits.const 5)) (fun _ => rfl))

/-- The literal of a listed coordinate at a cell is eventually day-small.
Source: bli-found `Emitter.machineSentenceCodes_eventually_small`
Kind: L
Fidelity: n/a -/
theorem cellSentence_eventually_small (c r : ℕ) :
    ∃ N, ∀ n ≥ N, SmallOn n (cellSentence 𝗜𝚺₁ halfRound halfRound_computable (n + 1) c r) :=
  machineSentenceCodes_eventually_small (cellSentence_machineSentenceCodes c r)

/-- **The pinned set of the fixed grid is eventually both coordinates** (K1's deliverable):
from some day `N` on, `⌜⊥⌝` and `⌜⊤⌝` are pinned.
Source: mandate K1 (pinned set non-empty); [[bli-program-desiderata]] §10 item 10
Kind: L
Fidelity: exact (`∃ N`; no numeral)
Hyps: (a) -/
theorem pinned_eventually_B2 (rep : ℕ → ℕ → ℚ) :
    ∃ N, ∀ n ≥ N, Encodable.encode (⊥ : Sentence) ∈ pinned (fixedCF rep) witnessIndex n ∧
      Encodable.encode (⊤ : Sentence) ∈ pinned (fixedCF rep) witnessIndex n := by
  obtain ⟨N₀, h₀⟩ := cellSentence_eventually_small (Encodable.encode (⊥ : Sentence)) 0
  obtain ⟨N₁, h₁⟩ := cellSentence_eventually_small (Encodable.encode (⊥ : Sentence)) 1
  obtain ⟨N₂, h₂⟩ := cellSentence_eventually_small (Encodable.encode (⊤ : Sentence)) 0
  obtain ⟨N₃, h₃⟩ := cellSentence_eventually_small (Encodable.encode (⊤ : Sentence)) 1
  refine ⟨max (max N₀ N₁) (max N₂ N₃), fun n hn => ?_⟩
  have hn0 : N₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : N₃ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  constructor <;> rw [mem_pinned] <;> refine ⟨by simp [witnessIndex], fun r hr => ?_⟩ <;>
    simp only [fixedCF, cellFamilyB2_cells, twoCells, Finset.mem_insert, Finset.mem_singleton] at hr <;>
    rw [fixedCF, cellFamilyB2_literal, sentenceOfCode_encode]
  · rcases hr with rfl | rfl
    · exact h₀ n hn0
    · exact h₁ n hn1
  · rcases hr with rfl | rfl
    · exact h₂ n hn2
    · exact h₃ n hn3

/-! ## Scope of the two coordinates -/

/-- `⊤` is small from day `1` on.
Source: none: infrastructure (bli-trajectory `Partition.top_mem_smallSet`, re-proved)
Kind: L
Fidelity: n/a -/
lemma verum_mem_smallSet {n : ℕ} (hn : 1 ≤ n) : (⊤ : Sentence) ∈ smallSet n := by
  rw [mem_smallSet]; unfold SmallOn; rw [tokenSize_verum]; exact four_le_sizeBound hn

/-- `⊤` is in every `Sminus n m` from day `1` on (no atoms).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma verum_mem_Sminus {n : ℕ} (hn : 1 ≤ n) (m : ℕ) : (⊤ : Sentence) ∈ Sminus n m := by
  rw [mem_Sminus]
  refine ⟨by rw [← mem_smallSet]; exact verum_mem_smallSet hn, fun a ha => ?_⟩
  simp at ha

/-- No atom is small on day `0` (`sizeBound 0 = 2 < 3 ≤ tokenSize`), so a pinned coordinate's
day is `≥ 1`.
Source: bli-found F-9 (day `0` is special)
Kind: L
Fidelity: n/a -/
lemma one_le_of_mem_pinned {rep : ℕ → ℕ → ℚ} {n c : ℕ}
    (hc : c ∈ pinned (fixedCF rep) witnessIndex n) : 1 ≤ n := by
  by_contra h
  have hn : n = 0 := by omega
  subst hn
  have := ((mem_pinned _ _ _ _).1 hc).2 0 (by simp [fixedCF, twoCells])
  unfold SmallOn at this
  rw [fixedCF, cellFamilyB2_literal] at this
  have h3 := three_le_tokenSize_atom (quotationClaimCode universalQuotePos universalQuoteNeg
    (Nat.pair (cellQuote 𝗜𝚺₁ halfRound halfRound_computable).code
      (Nat.pair 1 (Nat.pair (Encodable.encode (sentenceOfCode c)) 0))))
  have hs : sizeBound 0 = 2 := rfl
  rw [hs] at this
  exact absurd (le_trans h3 this) (by norm_num)

/-- **The pinned coordinates are small today and in faith's scope** (the scope condition of
`d_nnucell_of_package`, discharged on the fixed grid).
Source: mandate K2 ("state both")
Kind: L
Fidelity: n/a -/
theorem fixed_scope (rep : ℕ → ℕ → ℚ) (n : ℕ) : ∀ c ∈ pinned (fixedCF rep) witnessIndex n,
    sentenceOfCode c ∈ smallSet n ∧ sentenceOfCode c ∈ Sminus (n + 1) (n + 1) := by
  intro c hc
  have hn := one_le_of_mem_pinned hc
  rcases mem_witnessIndex_iff.1 ((mem_pinned _ _ _ _).1 hc).1 with rfl | rfl
  · rw [sentenceOfCode_encode]; exact ⟨falsum_mem_smallSet n, falsum_mem_Sminus _ _⟩
  · rw [sentenceOfCode_encode]
    exact ⟨verum_mem_smallSet hn, verum_mem_Sminus (by omega) _⟩

/-! ## The headline instance -/

/-- **K2 at B2 (the determination theorem of record, instantiated).** Over `paperDP 𝗜𝚺₁`, the
two-cell rounding and the fixed four-table grid over `[⌜⊥⌝, ⌜⊤⌝]` with representatives `rep`: if
a superbelief `P` is a stage-level world mixture on the day-`n` small sentences and the B2
state sentences (`PCPσ`), partitions (`E5σ`), agrees with a base `Q` on the small sentences
(`E1x`) and has exact faith in the written-out states (`E2xσ`), then `Q` satisfies exact
finite-time no-net-expected-update on every pinned coordinate — and from some day on both
coordinates are pinned (`pinned_eventually_B2`). Any `Q`, FAF's LIA included; nothing says the
LIA is linked. **Vacuity warning:** with `bli-found`'s `witnessRep` the hypothesis package is
unsatisfiable (`fixedSystem_witnessRep_unsat`: faith at `⊥` pins every charged candidate's
value at `⊥` to `0`, and `witnessRep` never is `0`); with representatives `0`/`1` faith at `⊥`
and `⊤` pins the charged candidate to the single table `tbl 0 1` (`Faith.faith_at_falsum`,
`faith_at_verum`), so no two-state charge exists on this index at all. The non-degenerate
inhabitant of the package is `Witness.determination_package_inhabited`, over an uncertain
coordinate.
Source: [[bli-program]] §3.6(ii); [[bli-program-desiderata]] I6; mandate K2 (judged item 1)
Kind: C
Fidelity: exact (stage level, on the fixed grid; `∃ N` for the pinned set; see the vacuity warning)
Hyps: (a) -/
theorem d_nnucell_B2 (rep : ℕ → ℕ → ℚ) {atoms : ℕ → Finset ℕ} {P Q : History}
    (hatoms : ∀ n, stateAtoms σB2 (fixedSystemR rep) n ⊆ atoms n)
    (hcoh : PCPσ atoms (paperDP 𝗜𝚺₁) P) (hE5 : E5σ σB2 (fixedSystemR rep) P) (hE1 : E1x Q P)
    (hE2 : E2xσ σB2 (fixedSystemR rep) P) :
    D_NNUcell (fixedCF rep) witnessIndex Q := by
  have hσ : ∀ m, ∀ q ∈ (fixedSystemR rep).states m, stateOf (fixedCF rep) m q = σB2 m q :=
    fun m q hq => stateOf_fixedCF_eq rep m hq
  refine d_nnucell_of_package (fixedCF rep) hcoh
    (fun n => by rw [stateAtoms_congr hσ]; exact hatoms n)
    ((E5σ_congr hσ).2 hE5) hE1 ((E2xσ_congr hσ).2 hE2) (fixedStates_spuriousEntails rep)
    (fixedSystem_valuesAtRep rep) (fixed_scope rep)

/-- **The trilemma's horn (0) at B2**: over a base violating `D_NNUcell` on the fixed grid, no
superbelief satisfies `PCPσ ∧ E1x ∧ E2xσ ∧ E5σ` at the B2 state sentence.
Source: [[bli-program]] §3.6(ii); mandate K2 (T0)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem trilemma_T0_B2 (rep : ℕ → ℕ → ℚ) {atoms : ℕ → Finset ℕ} {P Q : History}
    (hatoms : ∀ n, stateAtoms σB2 (fixedSystemR rep) n ⊆ atoms n)
    (hviol : ¬ D_NNUcell (fixedCF rep) witnessIndex Q) :
    ¬ (PCPσ atoms (paperDP 𝗜𝚺₁) P ∧ E1x Q P ∧ E2xσ σB2 (fixedSystemR rep) P ∧
      E5σ σB2 (fixedSystemR rep) P) := by
  rintro ⟨hcoh, hE1, hE2, hE5⟩
  exact hviol (d_nnucell_B2 rep hatoms hcoh hE5 hE1 hE2)

/-! ## The vacuity finding: `bli-found`'s witness representatives -/

/-- Every fixed table values `⊥` at a representative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fixedSystemR_val_falsum (rep : ℕ → ℕ → ℚ) (m : ℕ) {q : ℕ} (hq : q ∈ fixedStates m) :
    ∃ a, a ≤ 1 ∧ (fixedSystemR rep).val m q ⊥ = (rep m a : ℝ) := by
  obtain ⟨a, b, ha, -, rfl⟩ := (mem_fixedStates_iff (m := m)).1 hq
  refine ⟨a, ha, ?_⟩
  show ((((entryOf (Encodable.encode (⊥ : Sentence)) (tableOfCode _)).map (rep m)).getD 0 : ℚ) : ℝ) = _
  rw [tableOfCode_encode, entryOf_tbl_bot]
  rfl

/-- **`bli-found`'s witness grid admits no faithful coherent partition.** With representatives
never `0` (`witnessRep`: `1/4`, `3/4`), `PCPσ ∧ E5σ ∧ E2xσ` at the B2 state sentence over
`fixedSystem` is unsatisfiable, for every `P` and every atom set: faith at `⊥ ∈ Sminus m m` pins
every charged candidate's value at `⊥` to `0`. So `d_nnucell_B2 witnessRep` is vacuous, and the
mandate's "N+: `Grid.fixedSystem` … with a `P` that is a mixture of ≥ 2 … worlds" cannot be met
on this index with these representatives — a finding about the witness grid, not about the
theorems.
Source: this package (findings); bli-found T7 witness (`witnessRep`, `fixedSystem`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem fixedSystem_witnessRep_unsat {atoms : ℕ → Finset ℕ} {P : History}
    (hatoms : ∀ n, stateAtoms σB2 fixedSystem n ⊆ atoms n) :
    ¬ (PCPσ atoms (paperDP 𝗜𝚺₁) P ∧ E5σ σB2 fixedSystem P ∧ E2xσ σB2 fixedSystem P) := by
  refine package_unsat_of_val_falsum_ne_zero hatoms 0 fun q hq => ?_
  rw [fixedSystem_eq] at hq ⊢
  obtain ⟨a, ha, hv⟩ := fixedSystemR_val_falsum witnessRep 1 hq
  rw [hv]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl <;> norm_num [witnessRep]

end Cleanroom.Bli.BliLinkageB
