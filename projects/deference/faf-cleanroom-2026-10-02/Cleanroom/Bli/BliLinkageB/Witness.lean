import Cleanroom.Bli.BliLinkageB.Dissolve

/-!
# bli-linkage, angle B — the N+ witness for the determination theorem's hypothesis package

`Determination.d_nnucell_of_package` has a hypothesis package (`PCPσ`, `E5σ`, `E1x`, `E2xσ`,
`SpuriousEntails`, `ValuesAtRep`, the scope condition) that must be shown inhabited by something
non-degenerate, and `Bracket.bracket_balance` likewise. This module inhabits both with **one**
market: the dissolution's four worlds with the literal index **linked to the price** (`a = 0` at
price `1/8`, `a = 1` at `7/8`), the state family now the cell-literal conjunction `stateOf wCF`
(the B2 shape), faith as conditioning, the same process `dDP`.

Everything the theorems predict then holds — `D_NNUcell` (checked directly:
`wP n φ₀ = 1/2 = 1/4 · 1/2 + 3/4 · 1/2`) and the two-sided bracket balance at an explicit
outer/inner family (tight on the inner side) — with two candidates of distinct tables, each of
mass `1/2`, two cells, the base uncertain about the coordinate and about tomorrow's cell.

The witness is abstract (the process `dDP` decides no price); the B2 instance over
`paperDP 𝗜𝚺₁`'s *stages* would need the day-`(n+1)` literals shown absent from `D n`, which the
mandate flags as likely to resist and this attempt did not do (see the report).
-/

namespace Cleanroom.Bli.BliLinkageB

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

namespace Witness

open Dissolve

/-! ## The cell family and the state family -/

/-- The witness's cell family over all witness worlds with literal index `≤ 1`: literals `dLit`,
cells `{0, 1}`, representatives `1/4, 3/4`; exclusive and exhaustive because exactly the
world's own literal holds.
Source: mandate § Definitions (`CellFamily`)
Kind: D
Fidelity: n/a -/
noncomputable def wCF :
    CellFamily (fun v => ∃ (x : ℚ) (b : Bool) (a : ℕ), a ≤ 1 ∧ v = wld x b a) where
  literal := dLit
  cells := dCells
  rep := dRep
  excl := by
    rintro m φ r r' hne v ⟨x, b, a, -, rfl⟩ ⟨h, h'⟩
    rw [wld_holds_dLit] at h h'
    exact hne (h.trans h'.symm)
  exh := by
    rintro m φ v ⟨x, b, a, ha, rfl⟩
    refine ⟨a, ?_, (wld_holds_dLit x b a m φ a).2 rfl⟩
    simp only [dCells, Finset.mem_insert, Finset.mem_singleton]; omega

/-- `wCF.literal`.
Source: none: witness
Kind: L
Fidelity: n/a -/
@[simp] lemma wCF_literal : wCF.literal = dLit := rfl

/-- `wCF.cells`.
Source: none: witness
Kind: L
Fidelity: n/a -/
@[simp] lemma wCF_cells : wCF.cells = dCells := rfl

/-- `wCF.rep`.
Source: none: witness
Kind: L
Fidelity: n/a -/
@[simp] lemma wCF_rep : wCF.rep = dRep := rfl

/-- The witness's state family: the cell-literal conjunction (the B2 shape).
Source: none: witness
Kind: D
Fidelity: n/a -/
noncomputable abbrev wσ : ℕ → ℕ → Sentence := stateOf wCF

/-- The state sentence of `dCode r` is the literal of the coordinate at `r` (conjoined with `⊤`).
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma wσ_dCode (m r : ℕ) : wσ m (dCode r) = dLit m dPhi r ⋏ ⊤ := by
  simp [stateOf, conjList]

/-- A witness world holds the state sentence of `dCode r` iff its literal index is `r`.
Source: none: witness
Kind: L
Fidelity: n/a -/
@[simp] lemma wld_holds_wσ (x : ℚ) (b : Bool) (a m r : ℕ) :
    (wld x b a).Holds (wσ m (dCode r)) ↔ r = a := by
  rw [wσ_dCode, PCWorld.holds_and, wld_holds_dLit]
  exact ⟨fun h => h.1, fun h => ⟨h, PCWorld.holds_top _⟩⟩

/-- Payout of the state sentence of the world's own cell: `1`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma payout_wσ_self (x : ℚ) (b : Bool) (a m : ℕ) : (wld x b a).payout (wσ m (dCode a)) = 1 :=
  payout_of_holds ((wld_holds_wσ x b a m a).2 rfl)

/-- Payout of the state sentence of another cell: `0`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma payout_wσ_ne (x : ℚ) (b : Bool) {a r : ℕ} (h : r ≠ a) (m : ℕ) :
    (wld x b a).payout (wσ m (dCode r)) = 0 :=
  payout_of_not_holds fun h' => h ((wld_holds_wσ x b a m r).1 h')

/-! ## The four price-linked worlds and the market -/

/-- The four worlds: price `1/8` with literal `0`, price `7/8` with literal `1`; coordinate true
or false.
Source: none: witness
Kind: D
Fidelity: n/a -/
def wWorld : Fin 4 → PCWorld
  | 0 => wld (1 / 8) true 0
  | 1 => wld (1 / 8) false 0
  | 2 => wld (7 / 8) true 1
  | 3 => wld (7 / 8) false 1

/-- Every world of the mixture is a witness world whose literal is the cell of its price.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma wWorld_eq (i : Fin 4) : ∃ (x : ℚ) (b : Bool) (a : ℕ), a ≤ 1 ∧ -1 < x ∧ x < 2 ∧
    (∀ m, dLo m a < x ∧ x < dHi m a) ∧ wWorld i = wld x b a :=
  match i with
  | 0 => ⟨1 / 8, true, 0, le_rfl.trans zero_le_one, by norm_num, by norm_num,
      fun m => (cell_facts m).1, rfl⟩
  | 1 => ⟨1 / 8, false, 0, le_rfl.trans zero_le_one, by norm_num, by norm_num,
      fun m => (cell_facts m).1, rfl⟩
  | 2 => ⟨7 / 8, true, 1, le_rfl, by norm_num, by norm_num, fun m => (cell_facts m).2.2.2, rfl⟩
  | 3 => ⟨7 / 8, false, 1, le_rfl, by norm_num, by norm_num, fun m => (cell_facts m).2.2.2, rfl⟩

/-- **The witness market**: the four price-linked worlds, weights `1/8, 3/8, 3/8, 1/8`.
Source: none: witness
Kind: D
Fidelity: n/a -/
noncomputable def wP : History := fun _ φ => ∑ i : Fin 4, dW i * (wWorld i).payout φ

/-- `wP` unfolded over the four worlds.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma wP_eq (n : ℕ) (φ : Sentence) :
    wP n φ = 1 / 8 * (wld (1 / 8) true 0).payout φ + 3 / 8 * (wld (1 / 8) false 0).payout φ +
      3 / 8 * (wld (7 / 8) true 1).payout φ + 1 / 8 * (wld (7 / 8) false 1).payout φ := by
  simp [wP, Fin.sum_univ_four, dW, wWorld]

/-- The state masses: each candidate has mass `1/2`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma wP_state (n m : ℕ) : wP n (wσ m (dCode 0)) = 1 / 2 ∧ wP n (wσ m (dCode 1)) = 1 / 2 := by
  have h01 : (0 : ℕ) ≠ 1 := by norm_num
  constructor
  · rw [wP_eq, payout_wσ_self, payout_wσ_self, payout_wσ_ne _ _ h01, payout_wσ_ne _ _ h01]
    norm_num
  · rw [wP_eq, payout_wσ_ne _ _ h01.symm, payout_wσ_ne _ _ h01.symm, payout_wσ_self,
      payout_wσ_self]
    norm_num

/-- The coordinate's price is `1/2`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma wP_dPhi (n : ℕ) : wP n dPhi = 1 / 2 := by
  rw [wP_eq, payout_dPhi_true, payout_dPhi_false, payout_dPhi_true, payout_dPhi_false]
  norm_num

/-- The literal prices: `1/2` each.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma wP_dLit (n m : ℕ) (φ : Sentence) :
    wP n (dLit m φ 0) = 1 / 2 ∧ wP n (dLit m φ 1) = 1 / 2 := by
  have h01 : (0 : ℕ) ≠ 1 := by norm_num
  constructor
  · rw [wP_eq, payout_dLit_self, payout_dLit_self, payout_dLit_ne _ _ h01, payout_dLit_ne _ _ h01]
    norm_num
  · rw [wP_eq, payout_dLit_ne _ _ h01.symm, payout_dLit_ne _ _ h01.symm, payout_dLit_self,
      payout_dLit_self]
    norm_num

/-! ## The state system -/

/-- **Values as conditional probabilities given the state** (as in `Dissolve.dVal`).
Source: none: witness
Kind: D
Fidelity: n/a -/
noncomputable def wVal (_m q : ℕ) (φ : Sentence) : ℝ :=
  if q = dCode 0 then
    2 * (1 / 8 * (wld (1 / 8) true 0).payout φ + 3 / 8 * (wld (1 / 8) false 0).payout φ)
  else if q = dCode 1 then
    2 * (3 / 8 * (wld (7 / 8) true 1).payout φ + 1 / 8 * (wld (7 / 8) false 1).payout φ)
  else 0

/-- The witness state system.
Source: none: witness
Kind: D
Fidelity: n/a -/
noncomputable def wS : StateSystem where
  states := dStates
  val := wVal
  actual _ := dCode 1
  actual_mem _ := by simp [dStates]

/-- `wS.states`.
Source: none: witness
Kind: L
Fidelity: n/a -/
@[simp] lemma wS_states : wS.states = dStates := rfl

/-- `wS.val`.
Source: none: witness
Kind: L
Fidelity: n/a -/
@[simp] lemma wS_val : wS.val = wVal := rfl

/-- `wVal` at `dCode 0`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma wVal_zero (m : ℕ) (φ : Sentence) : wVal m (dCode 0) φ =
    2 * (1 / 8 * (wld (1 / 8) true 0).payout φ + 3 / 8 * (wld (1 / 8) false 0).payout φ) := by
  rw [wVal, if_pos rfl]

/-- `wVal` at `dCode 1`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma wVal_one (m : ℕ) (φ : Sentence) : wVal m (dCode 1) φ =
    2 * (3 / 8 * (wld (7 / 8) true 1).payout φ + 1 / 8 * (wld (7 / 8) false 1).payout φ) := by
  rw [wVal, if_neg dCode_zero_ne_one.symm, if_pos rfl]

/-- The values at the coordinate are the representatives.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma wVal_dPhi (m : ℕ) : wVal m (dCode 0) dPhi = 1 / 4 ∧ wVal m (dCode 1) dPhi = 3 / 4 := by
  constructor
  · rw [wVal_zero, payout_dPhi_true, payout_dPhi_false]; norm_num
  · rw [wVal_one, payout_dPhi_true, payout_dPhi_false]; norm_num

/-! ## The package -/

/-- A price-linked witness world is linked at the state family `wσ`: holding the state of cell
`a` means the literal index is `a`, and the price lies in cell `a`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma wld_linkedWorld_w {x : ℚ} (h1 : -1 < x) (h2 : x < 2) (b : Bool) {a : ℕ}
    (hcell : ∀ m, dLo m a < x ∧ x < dHi m a) (m : ℕ) :
    LinkedWorld wσ dQuote wS (cellOfTable dLo dHi) m (wld x b a) := by
  intro q hq φ _ hs
  rw [wS_states, mem_dStates] at hq
  rcases hq with rfl | rfl <;>
  · rw [cellOfTable_dCode]
    rw [wld_holds_wσ] at hs
    subst hs
    by_cases h : Encodable.encode φ = dC0
    · rw [if_pos h]; exact (wld_holds_dQuote _ _ _ _ _ _ _).2 (hcell m)
    · rw [if_neg h]; exact (wld_holds_dQuote _ _ _ _ _ _ _).2 ⟨h1, h2⟩

/-- **`PCPσTheory` holds** (every atom set).
Source: mandate K2 (witness)
Kind: L
Fidelity: n/a -/
theorem wPCPσTheory (atoms : ℕ → Finset ℕ) : PCPσTheory atoms dDP wP := by
  intro n
  refine ⟨4, wWorld, dW, fun i => ?_, dW_nonneg, dW_sum, fun _ _ => rfl⟩
  obtain ⟨x, b, a, -, h1, h2, -, h⟩ := wWorld_eq i
  rw [h]; exact wld_consistentWithTheory h1 h2 b a

/-- **`PCPσ` holds** (every atom set).
Source: mandate K2 (witness)
Kind: L
Fidelity: n/a -/
theorem wPCPσ (atoms : ℕ → Finset ℕ) : PCPσ atoms dDP wP := (wPCPσTheory atoms).toPCPσ

/-- **`PCPσLinked` holds** (every atom set).
Source: mandate K2 (witness)
Kind: L
Fidelity: n/a -/
theorem wPCPσLinked (atoms : ℕ → Finset ℕ) :
    PCPσLinked wσ dQuote wS (cellOfTable dLo dHi) atoms dDP wP := by
  intro n
  refine ⟨4, wWorld, dW, fun i => ?_, dW_nonneg, dW_sum, fun _ _ => rfl⟩
  obtain ⟨x, b, a, -, h1, h2, hcell, h⟩ := wWorld_eq i
  rw [h]
  exact ⟨wld_consistentWithTheory h1 h2 b a n, wld_linkedWorld_w h1 h2 b hcell _,
    wld_intervalSem x b a⟩

/-- **`E1x` holds** with the base `wP` itself.
Source: mandate K2 (witness)
Kind: L
Fidelity: n/a -/
theorem wE1x : E1x wP wP := fun _ _ _ => rfl

/-- **`E5σ` holds**: masses `1/2 + 1/2`; no world holds two states.
Source: mandate K2 (witness)
Kind: L
Fidelity: n/a -/
theorem wE5σ : E5σ wσ wS wP := by
  intro n
  have h01 : (0 : ℕ) ≠ 1 := by norm_num
  have hex : ∀ b : Bool, ∀ (x : ℚ) (a : ℕ), a ≤ 1 →
      (wld x b a).payout (wσ (n + 1) (dCode 0) ⋏ wσ (n + 1) (dCode 1)) = 0 := by
    intro b x a ha
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
    · rw [payout_and, payout_wσ_ne _ _ h01.symm, mul_zero]
    · rw [payout_and, payout_wσ_ne _ _ h01, zero_mul]
  have hex' : ∀ b : Bool, ∀ (x : ℚ) (a : ℕ), a ≤ 1 →
      (wld x b a).payout (wσ (n + 1) (dCode 1) ⋏ wσ (n + 1) (dCode 0)) = 0 := by
    intro b x a ha
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
    · rw [payout_and, payout_wσ_ne _ _ h01.symm, zero_mul]
    · rw [payout_and, payout_wσ_ne _ _ h01, mul_zero]
  constructor
  · rw [wS_states, dStates, Finset.sum_pair dCode_zero_ne_one, (wP_state n (n + 1)).1,
      (wP_state n (n + 1)).2]
    norm_num
  · intro q₁ hq₁ q₂ hq₂ hne
    rw [wS_states, mem_dStates] at hq₁ hq₂
    rcases hq₁ with rfl | rfl <;> rcases hq₂ with rfl | rfl
    · exact absurd rfl hne
    · rw [wP_eq, hex _ _ 0 (by norm_num), hex _ _ 0 (by norm_num), hex _ _ 1 le_rfl,
        hex _ _ 1 le_rfl]
      norm_num
    · rw [wP_eq, hex' _ _ 0 (by norm_num), hex' _ _ 0 (by norm_num), hex' _ _ 1 le_rfl,
        hex' _ _ 1 le_rfl]
      norm_num
    · exact absurd rfl hne

/-- **`E2xσ` holds, at every sentence**: faith is conditioning.
Source: mandate K2 (witness); bli-found F-12
Kind: L
Fidelity: n/a -/
theorem wE2xσ : E2xσ wσ wS wP := by
  intro n m _ q hq φ _
  have h01 : (0 : ℕ) ≠ 1 := by norm_num
  rw [wS_states, mem_dStates] at hq
  rcases hq with rfl | rfl
  · rw [wP_eq, wP_eq, wS_val, wVal_zero]
    simp only [payout_and, payout_wσ_self, payout_wσ_ne _ _ h01]
    ring
  · rw [wP_eq, wP_eq, wS_val, wVal_one]
    simp only [payout_and, payout_wσ_self, payout_wσ_ne _ _ h01.symm]
    ring

/-- **`SpuriousEntails` holds** on the two-candidate grid: the candidate of cell `a` with the
literal of cell `r ≠ a` entails the candidate of cell `r`.
Source: this package (`Defs.SpuriousEntails`)
Kind: L
Fidelity: n/a -/
theorem wSpuriousEntails (n : ℕ) : SpuriousEntails wσ dLit wS dIndex dCells n := by
  intro q hq c hc r hr hne
  rw [wS_states, mem_dStates] at hq
  simp only [dIndex, List.mem_singleton] at hc
  subst hc
  have hr1 : r ≤ 1 := by
    simp only [dCells, Finset.mem_insert, Finset.mem_singleton] at hr; omega
  have key : ∀ a, a ≤ 1 → q = dCode a → ∃ q' ∈ wS.states (n + 1), q' ≠ q ∧
      ∀ v : PCWorld, v.Holds (wσ (n + 1) q) → v.Holds (dLit (n + 1) (sentenceOfCode dC0) r) →
        v.Holds (wσ (n + 1) q') := by
    rintro a ha rfl
    rw [tableOfCode_dCode] at hne
    have har : a ≠ r := fun h => hne (by simp [entryOf, h])
    refine ⟨dCode r, ?_, fun h => har (dCode_inj.1 h).symm, fun v _ hl => ?_⟩
    · rw [wS_states, mem_dStates]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hr1 with rfl | rfl <;> simp
    · rw [wσ_dCode, PCWorld.holds_and]
      rw [sentenceOfCode_dC0] at hl
      exact ⟨hl, PCWorld.holds_top _⟩
  rcases hq with rfl | rfl
  · exact key 0 (by norm_num) rfl
  · exact key 1 le_rfl rfl

/-- **`ValuesAtRep` holds**: each candidate values the coordinate at its representative.
Source: mandate K2 (`hval`)
Kind: L
Fidelity: n/a -/
theorem wValuesAtRep (n : ℕ) : ValuesAtRep wCF wS dIndex n := by
  intro q hq c hc
  simp only [dIndex, List.mem_singleton] at hc
  subst hc
  rw [wS_states, mem_dStates] at hq
  rcases hq with rfl | rfl
  · refine ⟨0, by simp [dCells], by simp [entryOf], ?_⟩
    rw [wS_val, sentenceOfCode_dC0, (wVal_dPhi (n + 1)).1, wCF_rep, dRep]
    norm_num
  · refine ⟨1, by simp [dCells], by simp [entryOf], ?_⟩
    rw [wS_val, sentenceOfCode_dC0, (wVal_dPhi (n + 1)).2, wCF_rep, dRep]
    norm_num

/-! ## Scope of the coordinate -/

/-- `atom 0` is small on every day `≥ 1` (bli-trajectory's `cohAtom_smallOn`, re-proved).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma dPhi_smallOn {m : ℕ} (hm : 1 ≤ m) : SmallOn m dPhi := by
  unfold SmallOn dPhi
  rw [tokenSize_atom]
  have h := length_natDigits4_le_of_lt_pow (n := 0 + 5) (L := 2) (by norm_num)
  have := four_le_sizeBound hm
  omega

/-- `atomDay 0 = 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atomDay_zero' : atomDay 0 = 0 := by
  simp [atomDay, atomDayBase, cleanroomBaseTag, Nat.unpair_zero]

/-- `atom 0 ∈ Sminus m m` for every `m ≥ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma dPhi_mem_Sminus {m : ℕ} (hm : 1 ≤ m) : dPhi ∈ Sminus m m := by
  rw [mem_Sminus]
  refine ⟨dPhi_smallOn hm, fun a ha => ?_⟩
  simp only [dPhi, sentenceAtomCodes_atom, Finset.mem_singleton] at ha
  subst ha
  rw [atomDay_zero']
  omega

/-- No literal is small on day `0`, so a pinned day is `≥ 1`.
Source: bli-found F-9
Kind: L
Fidelity: n/a -/
lemma one_le_of_mem_pinned_w {n c : ℕ} (hc : c ∈ pinned wCF dIndex n) : 1 ≤ n := by
  by_contra h
  have hn : n = 0 := by omega
  subst hn
  have := ((mem_pinned _ _ _ _).1 hc).2 0 (by simp [dCells])
  unfold SmallOn at this
  rw [wCF_literal, dLit] at this
  have h3 := three_le_tokenSize_atom (lIdx 1 (Encodable.encode (sentenceOfCode c)) 0)
  have hs : sizeBound 0 = 2 := rfl
  rw [hs] at this
  exact absurd (le_trans h3 this) (by norm_num)

/-- **The pinned coordinate is small today and in faith's scope.**
Source: mandate K2 ("state both")
Kind: L
Fidelity: n/a -/
theorem wScope (n : ℕ) : ∀ c ∈ pinned wCF dIndex n,
    sentenceOfCode c ∈ smallSet n ∧ sentenceOfCode c ∈ Sminus (n + 1) (n + 1) := by
  intro c hc
  have hn := one_le_of_mem_pinned_w hc
  have hc' : c = dC0 := by
    have := ((mem_pinned _ _ _ _).1 hc).1
    simpa [dIndex] using this
  subst hc'
  rw [sentenceOfCode_dC0]
  exact ⟨by rw [mem_smallSet]; exact dPhi_smallOn hn, dPhi_mem_Sminus (by omega)⟩

/-- The pinned set is eventually the coordinate (the literal family is the same as the
dissolution's).
Source: mandate K1 (pinned set non-empty)
Kind: L
Fidelity: n/a -/
theorem wPinned_eventually : ∃ N, ∀ n ≥ N, dC0 ∈ pinned wCF dIndex n := by
  obtain ⟨N₀, h₀⟩ := dLit_eventually_small 0
  obtain ⟨N₁, h₁⟩ := dLit_eventually_small 1
  refine ⟨max N₀ N₁, fun n hn => ?_⟩
  rw [mem_pinned]
  refine ⟨by simp [dIndex], fun r hr => ?_⟩
  rw [wCF_cells, dCells, Finset.mem_insert, Finset.mem_singleton] at hr
  rw [wCF_literal, sentenceOfCode_dC0]
  rcases hr with rfl | rfl
  · exact h₀ n (le_trans (le_max_left _ _) hn)
  · exact h₁ n (le_trans (le_max_right _ _) hn)

/-! ## The determination theorem, inhabited and checked -/

/-- **N+ for `d_nnucell_of_package`**: the full hypothesis package is inhabited, with two
candidates of distinct tables each of mass `1/2`, two cells and the base at `1/2` on the
coordinate; the theorem's conclusion `D_NNUcell wCF dIndex wP` follows.
Source: mandate K2 (judged item 1: "N+"); [[STANDARDS]] §3 (non-vacuity)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem determination_package_inhabited :
    PCPσ (stateAtoms wσ wS) dDP wP ∧ E5σ wσ wS wP ∧ E1x wP wP ∧ E2xσ wσ wS wP ∧
      (∀ n, SpuriousEntails wσ dLit wS dIndex dCells n) ∧ (∀ n, ValuesAtRep wCF wS dIndex n) ∧
      (∃ N, ∀ n ≥ N, dC0 ∈ pinned wCF dIndex n) ∧
      dCode 0 ≠ dCode 1 ∧ (∀ n, 0 < wP n (wσ (n + 1) (dCode 0)) ∧ 0 < wP n (wσ (n + 1) (dCode 1))) ∧
      (∀ n, wP n dPhi = 1 / 2) ∧
      D_NNUcell wCF dIndex wP :=
  ⟨wPCPσ _, wE5σ, wE1x, wE2xσ, wSpuriousEntails, wValuesAtRep, wPinned_eventually,
    dCode_zero_ne_one,
    fun n => ⟨by rw [(wP_state n (n + 1)).1]; norm_num, by rw [(wP_state n (n + 1)).2]; norm_num⟩,
    wP_dPhi,
    d_nnucell_of_package wCF (wPCPσ _) (fun _ => subset_rfl) wE5σ wE1x wE2xσ wSpuriousEntails
      wValuesAtRep wScope⟩

/-- **The identity, checked directly**: `wP n φ₀ = 1/2 = 1/4 · 1/2 + 3/4 · 1/2` — the
determination theorem's conclusion is exercised, not trivial (contrast `Dissolve.dNot_D_NNUcell`
on the same worlds with decoupled literals).
Source: mandate K2
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem d_nnucell_checked (n : ℕ) :
    wP n dPhi = ∑ r ∈ dCells (n + 1), (dRep (n + 1) r : ℝ) * wP n (dLit (n + 1) dPhi r) := by
  rw [wP_dPhi, dCells, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1), (wP_dLit n (n + 1) dPhi).1,
    (wP_dLit n (n + 1) dPhi).2]
  norm_num [dRep]

/-! ## The bracket balance, inhabited -/

/-- A witness quote of the coordinate at fixed endpoints is a machine-metered family in the day
(an atom over a `Nat.pair`-nest of the day and constants), hence eventually day-small.
Source: bli-found `Emitter.machineSentenceCodes_eventually_small`
Kind: L
Fidelity: n/a -/
theorem dQuote_eventually_small (lo hi : ℚ) :
    ∃ N, ∀ n ≥ N, dQuote (n + 1) dPhi lo hi ∈ smallSet n := by
  have hd : MachineDigits fun n => qIdx (n + 1) dC0 lo hi :=
    (MachineDigits.natPair (MachineDigits.const (cleanroomBaseTag + quoteFam))
      (MachineDigits.natPair ((MachineDigits.ofUnaryRuler UnaryRuler.id).add (MachineDigits.const 1))
        (MachineDigits.natPair (MachineDigits.const dC0)
          (MachineDigits.const (Encodable.encode (lo, hi)))))).of_eq (fun _ => rfl)
  have hm : MachineSentenceCodes fun n => dQuote (n + 1) dPhi lo hi :=
    MachineSentenceCodes.ofCanonical
      (MachineTokenStream.of_eq (hd.add (MachineDigits.const 5)) (fun _ => rfl))
  obtain ⟨N, hN⟩ := machineSentenceCodes_eventually_small hm
  exact ⟨N, fun n hn => by rw [mem_smallSet]; exact hN n hn⟩

/-- The outer family: `(-2, 3/4) ⊃ [-1, 1/2]` and `(0, 3) ⊃ [1/4, 2]`.
Source: none: witness
Kind: D
Fidelity: n/a -/
def outerI (r : ℕ) : ℚ × ℚ := if r = 0 then (-2, 3 / 4) else (0, 3)

/-- The inner family: `(-2, 1/5)` meets no cell but `0`; `(3/5, 3)` meets no cell but `1`.
Source: none: witness
Kind: D
Fidelity: n/a -/
def innerJ (r : ℕ) : ℚ × ℚ := if r = 0 then (-2, 1 / 5) else (3 / 5, 3)

/-- **N+ for `bracket_balance`**: on the witness market, from some day on, the two-sided bracket
balance holds at the outer/inner families — every hypothesis of `Bracket.bracket_balance` is
inhabited (linked coherent stage mixture with two charged states, partition, faith, small
agreement, codes, representatives in cells, the families' geometry, the quotes small).
Source: mandate § Attempt angles (B: the bracket balance); [[STANDARDS]] §3 (non-vacuity)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem bracket_balance_inhabited : ∃ N, ∀ n ≥ N,
    ∑ r ∈ dCells (n + 1), (dRep (n + 1) r : ℝ) * wP n (dQuote (n + 1) dPhi (innerJ r).1 (innerJ r).2)
        ≤ wP n dPhi ∧
      wP n dPhi ≤
        ∑ r ∈ dCells (n + 1), (dRep (n + 1) r : ℝ) * wP n (dQuote (n + 1) dPhi (outerI r).1 (outerI r).2) := by
  obtain ⟨N₀, h₀⟩ := dQuote_eventually_small (-2) (3 / 4)
  obtain ⟨N₁, h₁⟩ := dQuote_eventually_small 0 3
  obtain ⟨N₂, h₂⟩ := dQuote_eventually_small (-2) (1 / 5)
  obtain ⟨N₃, h₃⟩ := dQuote_eventually_small (3 / 5) 3
  refine ⟨max (max N₀ N₁) (max (max N₂ N₃) 1), fun n hn => ?_⟩
  have hn0 : N₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn2 : N₂ ≤ n :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hn
  have hn3 : N₃ ≤ n :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hn
  have hn4 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have key := bracket_balance (σ := wσ) (quote := dQuote) (S := wS) (atoms := stateAtoms wσ wS)
    (DP := dDP) (P := wP) (Q := wP) wCF dLo dHi (wPCPσLinked _) (fun _ => subset_rfl) wE5σ wE2xσ
    wE1x n (dIndexCodes (n + 1)) (wValuesAtRep n) (by simp [dIndex] : dC0 ∈ dIndex (n + 1))
    (by rw [sentenceOfCode_dC0, mem_smallSet]; exact dPhi_smallOn hn4)
    (by rw [sentenceOfCode_dC0]; exact dPhi_mem_Sminus (by omega))
    (fun r hr => by
      rw [wCF_rep]
      simp only [wCF_cells, dCells, Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl <;> norm_num [dRep])
    outerI innerJ
    (fun r hr => by
      simp only [wCF_cells, dCells, Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl <;> norm_num [outerI, dLo, dHi])
    (fun r hr r' hr' hne => by
      simp only [wCF_cells, dCells, Finset.mem_insert, Finset.mem_singleton] at hr hr'
      rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl <;>
        first | exact absurd rfl hne | norm_num [innerJ, dLo, dHi])
    (fun r hr => by
      simp only [wCF_cells, dCells, Finset.mem_insert, Finset.mem_singleton] at hr
      rw [sentenceOfCode_dC0]
      rcases hr with rfl | rfl
      · simpa [outerI] using h₀ n hn0
      · simpa [outerI] using h₁ n hn1)
    (fun r hr => by
      simp only [wCF_cells, dCells, Finset.mem_insert, Finset.mem_singleton] at hr
      rw [sentenceOfCode_dC0]
      rcases hr with rfl | rfl
      · simpa [innerJ] using h₂ n hn2
      · simpa [innerJ] using h₃ n hn3)
  rw [sentenceOfCode_dC0, wCF_cells, wCF_rep] at key
  exact key

end Witness

end Cleanroom.Bli.BliLinkageB
