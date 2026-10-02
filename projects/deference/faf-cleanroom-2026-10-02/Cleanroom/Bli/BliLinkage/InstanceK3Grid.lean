import Cleanroom.Bli.BliLinkage.InstanceK3

/-!
# `bli-linkage` — K3 at FAF's LIA over a one-coordinate grid listing a varying,
machine-metered coordinate family (repair round 2, audit r2 adversarial B2)

The family form `InstanceK3.no_degenerate_linked_bli_LIA_family` takes the index list and the
state system as parameters. The adversarial audit (B2) observed that the only grid the
package built — `fixedStates` over `witnessIndex = [⌜⊥⌝, ⌜⊤⌝]` — makes the family form's
`hpin ∧ hmove` contradictory for **every** coordinate family (`InstanceK3.family_hmove_false_on_witnessIndex`):
pinned on that index means `χ n ∈ {⌜⊥⌝, ⌜⊤⌝}` for all large `n`, and both rounded prices
settle (`tbl01_eventually`). So the instance of record had no instance data on which it said
anything. This module builds the grid that carries a varying family:

* **`oneIndex χ`** lists exactly `χ n` on day `n + 1`; **`oneStates χ`** has the two one-entry
  tables `[(χ n, 0)]`, `[(χ n, 1)]` on day `n + 1`; **`oneSystem χ rep`** is bli-found's
  `b2StateSystem` over them (the actual rounded table is one of the two,
  `actualCode_mem_oneStates`); **`degOne χ`** is the degenerate table listing `χ n` at
  today's rounding of the LIA's exact quote of `sentenceOfCode (χ n)`.
* **`oneStates_spuriousEntails`**: the grid condition holds (a one-entry table with the other
  literal at its coordinate entails the other one-entry table).
* **`oneIndex_pinned_eventually`**: for a machine-metered code family (`hχ`), the day-indexed
  literal family `n ↦ cellSentence (n+1) (χ n) r` is machine-metered
  (`cellSentence_day_family_machineSentenceCodes`, `MachineDigits.natPair` at the day ruler
  `UnaryRuler.id` and `hχ`), hence eventually day-small (bli-found's emitter bridge), so
  `χ n` is pinned from some day on.
* **`no_degenerate_linked_bli_LIA_oneCoord`** — the family form with every grid hypothesis
  discharged: its only hypotheses are the family's e.c. certificate `hχ` and `hmove`. This is
  what makes the family form an *instance* rather than a schema (audit r2 adversarial B2,
  option (ii)); the leak family becomes a candidate for this instance's `hmove` once a
  leak-quoting literal family exists (T7), as the open list says.
* **The point mass on this grid** (`pointMass_oneSystem_e5σ`, `pointMass_degOne_degenerate_iff`,
  `pointMass_oneCoord_package_iff_still`): with the base equal to the superbelief, the
  package `PCPσ ∧ E5σ ∧ E1x P P ∧ Degenerate` is inhabited by the point mass **iff the
  family's rounded price never moves** — an exact characterization of the no-move regime at
  the superbelief side. It is **not** an inhabitant of the instance's package, whose base is
  the LIA: that package is **empty** (`LiaPackage.not_lia_small_coherent_mixture_exists`,
  repair r3, audit r3 B1: the `E1x` conjunct would make the LIA list doubly-exponentially many
  tautologies a day), so `no_degenerate_linked_bli_LIA_oneCoord` is vacuous
  (`InstanceK3Local.no_degenerate_linked_bli_LIA_oneCoord_vacuous`); the instance with
  content is the local form `InstanceK3Local.no_degenerate_linked_bli_LIA_oneCoord_lit`.
  Note the gap it exposes: for the point-mass base one move on one day already
  empties the package, while the theorem needs infinitely many — the theorem's content
  (exploitation of a coherent inductor by the price-reading trader) is not about this base.

What is still not shipped: an inhabitant of `hmove` at the LIA (a machine-metered family
whose `halfRound` cell moves between days `n` and `n+1` infinitely often) — unknown in both
directions, not evidence of falsity (ledger, `InstanceK3` docstring).
-/

namespace Cleanroom.Bli.BliLinkage

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound
open Cleanroom.Bli.BliLinkageB (fixedCF twoCells halfRound_lt_two payout_of_holds
  payout_of_not_holds)

/-! ## The one-coordinate grid -/

/-- The one-entry table `[(c, a)]`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def oneTable (c a : ℕ) : List (ℕ × ℕ) := [(c, a)]

/-- `oneTable_inj`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma oneTable_inj {c a c' a' : ℕ} : oneTable c a = oneTable c' a' ↔ c = c' ∧ a = a' := by
  simp [oneTable]

/-- The entry of a one-entry table at its coordinate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma entryOf_oneTable (c a : ℕ) : entryOf c (oneTable c a) = some a := by
  simp [oneTable, entryOf]

/-- **The one-coordinate index**: `χ n` alone on day `n + 1` (nothing on day `0`). The intended
families list genuine sentence codes (`IndexCodes (oneIndex χ)`, i.e. `χ n = ⌜sentenceOfCode (χ n)⌝`):
`oneSystem`'s `actual` table quotes the raw code `χ n` (bli-found's `actualTable`), while
`degOne`, `hχ` and `hmove` quote `⌜sentenceOfCode (χ n)⌝`; the two agree exactly on genuine
codes, and no conjunct of the instance's package reads `actual` (audit r3 adversarial N4).
Source: mandate K3 ("with `χ n` listed and pinned eventually"); audit r2 adversarial B2 (fix (ii))
Kind: D
Fidelity: exact -/
def oneIndex (χ : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => [χ n]

/-- **The one-coordinate grid**: the two one-entry tables at `χ n` on day `n + 1` (the empty
table on day `0`, so that the actual table is always listed).
Source: audit r2 adversarial B2 (fix (ii): "the two one-entry tables")
Kind: D
Fidelity: exact -/
def oneStates (χ : ℕ → ℕ) : ℕ → Finset ℕ
  | 0 => {Encodable.encode ([] : List (ℕ × ℕ))}
  | n + 1 => {Encodable.encode (oneTable (χ n) 0), Encodable.encode (oneTable (χ n) 1)}

/-- Membership in the day-`(n+1)` grid.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_oneStates_succ_iff {χ : ℕ → ℕ} {n q : ℕ} :
    q ∈ oneStates χ (n + 1) ↔ ∃ a, a ≤ 1 ∧ q = Encodable.encode (oneTable (χ n) a) := by
  simp only [oneStates, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, zero_le_one, rfl⟩
    · exact ⟨1, le_rfl, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- The two day-`(n+1)` candidates are distinct codes.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma oneStates_codes_ne (χ : ℕ → ℕ) (n : ℕ) :
    Encodable.encode (oneTable (χ n) 0) ≠ Encodable.encode (oneTable (χ n) 1) := by
  intro h
  rw [Encodable.encode_inj, oneTable_inj] at h
  exact zero_ne_one h.2

/-- **The actual rounded table over the one-coordinate index is one of the two candidates.**
Source: none: infrastructure (bli-found `Grid.actualCode_mem_fixedStates`, the same step)
Kind: L
Fidelity: n/a -/
theorem actualCode_mem_oneStates (χ : ℕ → ℕ) (m : ℕ) :
    actualCode 𝗜𝚺₁ halfRound (oneIndex χ) m ∈ oneStates χ m := by
  cases m with
  | zero => simp [actualCode, actualTable, oneIndex, oneStates]
  | succ n =>
    rw [mem_oneStates_succ_iff]
    exact ⟨halfRound (n + 1) (marketValue 𝗜𝚺₁ (Nat.pair (n + 1) (χ n))), halfRound_le_one _ _,
      by simp [actualCode, actualTable, oneIndex, oneTable]⟩

/-- **The one-coordinate B2 system with representatives `rep`** (bli-found's `b2StateSystem`
over `oneIndex χ`, `oneStates χ`).
Source: bli-found `StateSentence.b2StateSystem`; audit r2 adversarial B2 (fix (ii))
Kind: D
Fidelity: exact -/
noncomputable def oneSystem (χ : ℕ → ℕ) (rep : ℕ → ℕ → ℚ) : StateSystem :=
  b2StateSystem 𝗜𝚺₁ halfRound (oneIndex χ) (oneStates χ) (actualCode_mem_oneStates χ) rep

/-- The system's candidates.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma oneSystem_states (χ : ℕ → ℕ) (rep : ℕ → ℕ → ℚ) :
    (oneSystem χ rep).states = oneStates χ := rfl

/-- A world holds the state sentence of a one-entry table iff it holds the entry's literal.
Source: none: infrastructure (`holds_stateOf` at a one-entry table)
Kind: L
Fidelity: n/a -/
lemma holds_stateOf_oneTable {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) (m c a : ℕ) (v : PCWorld) :
    v.Holds (stateOf C m (Encodable.encode (oneTable c a))) ↔
      v.Holds (C.literal m (sentenceOfCode c) a) := by
  rw [holds_stateOf, tableOfCode_encode]
  simp [oneTable]

/-- **The degenerate table of the one-coordinate instance**: `χ n` listed at today's rounding
of the LIA's exact quote of `sentenceOfCode (χ n)`.
Source: mandate K3 (`deg n` "copying today's rounded entries")
Kind: D
Fidelity: exact -/
noncomputable def degOne (χ : ℕ → ℕ) (n : ℕ) : ℕ :=
  Encodable.encode (oneTable (χ n)
    (halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode (χ n)))))))

/-- The degenerate table is a day-`(n+1)` candidate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma degOne_mem (χ : ℕ → ℕ) (rep : ℕ → ℕ → ℚ) (n : ℕ) :
    degOne χ n ∈ (oneSystem χ rep).states (n + 1) := by
  rw [oneSystem_states, mem_oneStates_succ_iff]
  exact ⟨_, halfRound_le_one _ _, rfl⟩

/-- The degenerate table's entry at `χ n` is today's rounded price.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma degOne_entry (χ : ℕ → ℕ) (n : ℕ) :
    entryOf (χ n) (tableOfCode (degOne χ n)) =
      some (halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode (χ n)))))) := by
  unfold degOne
  rw [tableOfCode_encode, entryOf_oneTable]

/-- **The one-coordinate grid has `SpuriousEntails`**: a one-entry table together with the
other literal at its coordinate entails the other one-entry table.
Source: this package (`Defs.SpuriousEntails`); attempt B `fixedStates_spuriousEntails` (the same step on two coordinates)
Kind: L
Fidelity: n/a -/
theorem oneStates_spuriousEntails (rep : ℕ → ℕ → ℚ) (χ : ℕ → ℕ) (n : ℕ) :
    SpuriousEntails (stateOf (fixedCF rep)) (fixedCF rep).literal (oneSystem χ rep) (oneIndex χ)
      (fixedCF rep).cells n := by
  intro q hq c hc r hr hne
  rw [oneSystem_states, mem_oneStates_succ_iff] at hq
  obtain ⟨a, -, rfl⟩ := hq
  have hc' : c = χ n := by simpa [oneIndex] using hc
  subst hc'
  rw [tableOfCode_encode, entryOf_oneTable] at hne
  have har : a ≠ r := fun h => hne (by rw [h])
  have hr1 : r ≤ 1 := by
    change r ∈ twoCells (n + 1) at hr
    simp only [twoCells, Finset.mem_insert, Finset.mem_singleton] at hr
    omega
  refine ⟨Encodable.encode (oneTable (χ n) r),
    (oneSystem_states χ rep).symm ▸ mem_oneStates_succ_iff.2 ⟨r, hr1, rfl⟩, ?_, ?_⟩
  · intro h
    rw [Encodable.encode_inj, oneTable_inj] at h
    exact har h.2.symm
  · intro v _ hl
    rw [holds_stateOf_oneTable]
    exact hl

/-! ## Pinned eventually -/

/-- **The day-indexed B2 literal family over a machine-metered coordinate family is
machine-metered**: `n ↦ cellSentence (n + 1) (χ' n) r` at `𝗜𝚺₁`, `halfRound`, for `χ'` with
`MachineDigits χ'` and a fixed cell `r`. The atom's code is a `Nat.pair`-nest of constants,
the day ruler plus one, `χ' n` and `r`. Attempt B's `cellSentence_machineSentenceCodes c r` is
the case `χ' := fun _ => c`.
Source: FAF `MachineDigits.natPair`/`ofUnaryRuler`/`add`/`const`, `UnaryRuler.id`; attempt B `cellSentence_machineSentenceCodes`
Kind: L
Fidelity: n/a -/
theorem cellSentence_day_family_machineSentenceCodes (χ' : ℕ → ℕ) (hχ : MachineDigits χ')
    (r : ℕ) :
    MachineSentenceCodes fun n =>
      cellSentence 𝗜𝚺₁ halfRound halfRound_computable (n + 1) (χ' n) r := by
  have hd : MachineDigits fun n => quotationClaimCode universalQuotePos universalQuoteNeg
      (Nat.pair (cellQuote 𝗜𝚺₁ halfRound halfRound_computable).code
        (Nat.pair (n + 1) (Nat.pair (χ' n) r))) :=
    (MachineDigits.natPair (MachineDigits.const 2)
      (MachineDigits.natPair (MachineDigits.const (Encodable.encode universalQuotePos))
        (MachineDigits.natPair (MachineDigits.const (Encodable.encode universalQuoteNeg))
          (MachineDigits.natPair
            (MachineDigits.const (cellQuote 𝗜𝚺₁ halfRound halfRound_computable).code)
            (MachineDigits.natPair
              ((MachineDigits.ofUnaryRuler UnaryRuler.id).add (MachineDigits.const 1))
              (MachineDigits.natPair hχ (MachineDigits.const r))))))).of_eq (fun _ => rfl)
  exact MachineSentenceCodes.ofCanonical
    (MachineTokenStream.of_eq (hd.add (MachineDigits.const 5)) (fun _ => rfl))

/-- **A machine-metered coordinate family is pinned on the one-coordinate index from some
day on**: both cell literals of `χ n` are eventually day-small (bli-found's emitter bridge on
`cellSentence_day_family_machineSentenceCodes`). `∃ N` only.
Source: mandate K3 ("with `χ n` listed and pinned eventually"); bli-found `Emitter.machineSentenceCodes_eventually_small`
Kind: C
Fidelity: exact (`∃ N`, no numeral)
Hyps: (a) -/
theorem oneIndex_pinned_eventually (rep : ℕ → ℕ → ℚ) (χ : ℕ → ℕ)
    (hχ : MachineDigits fun n => Encodable.encode (sentenceOfCode (χ n))) :
    ∃ N, ∀ n ≥ N, χ n ∈ pinned (fixedCF rep) (oneIndex χ) n := by
  obtain ⟨N₀, h₀⟩ := machineSentenceCodes_eventually_small
    (cellSentence_day_family_machineSentenceCodes _ hχ 0)
  obtain ⟨N₁, h₁⟩ := machineSentenceCodes_eventually_small
    (cellSentence_day_family_machineSentenceCodes _ hχ 1)
  refine ⟨max N₀ N₁, fun n hn => ?_⟩
  rw [mem_pinned]
  refine ⟨by simp [oneIndex], fun r hr => ?_⟩
  change r ∈ twoCells (n + 1) at hr
  simp only [twoCells, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl
  · exact h₀ n (le_of_max_le_left hn)
  · exact h₁ n (le_of_max_le_right hn)

/-! ## The instance -/

/-- **K3 at FAF's LIA over `paperDP 𝗜𝚺₁`, one-coordinate grid, every grid hypothesis
discharged.** `Q := liaHistory (paperDP 𝗜𝚺₁)` (FAF's `paperLIA`), the B2 cell family at
`halfRound` with any representatives, the index listing `χ n` on day `n + 1`, the two
one-entry candidate tables, the degenerate table listing `χ n` at today's rounding of the
LIA's exact quote of `sentenceOfCode (χ n)` (`degOne`), the extra atom set the candidates'
state atoms: **if the family's code family is machine-metered (`hχ`) and the LIA's rounded
price of `χ n` moves between days `n` and `n + 1` infinitely often (`hmove`)**, no `P`
satisfies `PCPσ ∧ E5σ ∧ E1x ∧ Degenerate` at the B2 state sentence. Pinning
(`oneIndex_pinned_eventually`), the grid condition (`oneStates_spuriousEntails`), the
degenerate table's shape and membership (`degOne_entry`, `degOne_mem`), metering, stage
entry and `hworld` are all discharged; `hχ` and `hmove` are the hypotheses. **This package
is empty — the theorem is vacuous** (repair r3, audit r3 B1): the `E1x` conjunct forces the
LIA to list every small tautology, doubly-exponentially many a day, against its polynomial
day-`n` support (`LiaPackage.not_lia_small_coherent_mixture_exists`), so the conclusion holds
with `hχ` and `hmove` dropped (`InstanceK3Local.no_degenerate_linked_bli_LIA_oneCoord_vacuous`);
`hmove` is not the operative hypothesis. Kept as the mandate's K3 shape, honestly labelled;
the instance with content is `InstanceK3Local.no_degenerate_linked_bli_LIA_oneCoord_lit`
(`E1xLit` in place of `E1x`). No inhabitant of `hmove` is shipped (module docstring).
Source: [[bli-program]] §3.6(iii); desiderata I2; mandate K3 ("with `χ n` listed and pinned eventually"); audit r2 adversarial B2 (fix (ii))
Kind: C
Fidelity: exact (`hmove` and the family's e.c. certificate `hχ` the only hypotheses; the grid is instance data built here)
Hyps: (a); `hmove` is the honest conditional of mandate § K3; `hχ` the family's certificate; **vacuous**: the package is empty at FAF's LIA (`LiaPackage.not_lia_small_coherent_mixture_exists`) -/
theorem no_degenerate_linked_bli_LIA_oneCoord (rep : ℕ → ℕ → ℚ) {P : History} (χ : ℕ → ℕ)
    (hχ : MachineDigits fun n => Encodable.encode (sentenceOfCode (χ n)))
    (hmove : Set.Infinite {n |
      halfRound (n + 1) (marketValue 𝗜𝚺₁ (Nat.pair (n + 1) (Encodable.encode (sentenceOfCode (χ n))))) ≠
        halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode (χ n)))))}) :
    ¬ (PCPσ (stateAtoms (stateOf (fixedCF rep)) (oneSystem χ rep)) (paperDP 𝗜𝚺₁) P ∧
      E5σ (stateOf (fixedCF rep)) (oneSystem χ rep) P ∧
      E1x (liaHistory (paperDP 𝗜𝚺₁)) P ∧ Degenerate (stateOf (fixedCF rep)) P (degOne χ)) := by
  obtain ⟨N, hN⟩ := oneIndex_pinned_eventually rep χ hχ
  exact no_degenerate_linked_bli_LIA_family rep (oneIndex χ) (oneSystem χ rep) χ hχ (degOne χ) N
    hN (degOne_mem χ rep) (degOne_entry χ) (oneStates_spuriousEntails rep χ)
    (fun _ => Finset.Subset.refl _) hmove

/-! ## The point mass on this grid: the no-move regime, exactly -/

/-- In a completed-theory world the payout of a one-entry table's state sentence is the
indicator of "`a` is the rounded day-`m` price of `χ`'s coordinate".
Source: bli-found `StateSentence.cellSentence_reflected`
Kind: L
Fidelity: n/a -/
lemma payout_stateOf_oneTable (rep : ℕ → ℕ → ℚ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁)) (m c a : ℕ) :
    v.payout (stateOf (fixedCF rep) m (Encodable.encode (oneTable c a))) =
      if halfRound m (marketValue 𝗜𝚺₁ (Nat.pair m (Encodable.encode (sentenceOfCode c)))) = a
        then 1 else 0 := by
  have hiff : v.Holds (stateOf (fixedCF rep) m (Encodable.encode (oneTable c a))) ↔
      halfRound m (marketValue 𝗜𝚺₁ (Nat.pair m (Encodable.encode (sentenceOfCode c)))) = a := by
    rw [holds_stateOf_oneTable]
    exact cellSentence_reflected 𝗜𝚺₁ halfRound halfRound_computable m _ a v hv
  split_ifs with h
  · exact payout_of_holds (hiff.2 h)
  · exact payout_of_not_holds fun hh => h (hiff.1 hh)

/-- **The point mass partitions at the B2 state sentence over the one-coordinate grid**:
exactly one of the two one-entry tables holds in a completed-theory world.
Source: mandate K1/K2 (`E5σ`); this run (repair r2)
Kind: L
Fidelity: n/a -/
theorem pointMass_oneSystem_e5σ (rep : ℕ → ℕ → ℚ) (χ : ℕ → ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁)) :
    E5σ (stateOf (fixedCF rep)) (oneSystem χ rep) (pointMass v) := by
  intro n
  have hle := halfRound_le_one (n + 1)
    (marketValue 𝗜𝚺₁ (Nat.pair (n + 1) (Encodable.encode (sentenceOfCode (χ n)))))
  constructor
  · show ∑ q ∈ ({Encodable.encode (oneTable (χ n) 0), Encodable.encode (oneTable (χ n) 1)} :
        Finset ℕ), v.payout (stateOf (fixedCF rep) (n + 1) q) = 1
    rw [Finset.sum_pair (oneStates_codes_ne χ n), payout_stateOf_oneTable rep v hv,
      payout_stateOf_oneTable rep v hv]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h <;> rw [h] <;> norm_num
  · intro q₁ hq₁ q₂ hq₂ hne
    rw [oneSystem_states, mem_oneStates_succ_iff] at hq₁ hq₂
    obtain ⟨a₁, ha₁, rfl⟩ := hq₁
    obtain ⟨a₂, ha₂, rfl⟩ := hq₂
    have hne' : a₁ ≠ a₂ := fun h => hne (by rw [h])
    show v.payout (stateOf (fixedCF rep) (n + 1) _ ⋏ stateOf (fixedCF rep) (n + 1) _) = 0
    rw [Cleanroom.Bli.BliLinkageB.payout_and, payout_stateOf_oneTable rep v hv,
      payout_stateOf_oneTable rep v hv]
    split_ifs with h₁ h₂
    · exact absurd (h₁.symm.trans h₂) hne'
    · exact mul_zero _
    · exact zero_mul _
    · exact zero_mul _

/-- **For the point mass, the `Degenerate` clause at `degOne` is exactly the no-move
condition**: `v` holds tomorrow's state "`χ n` rounds to today's cell" iff the rounded price
of `χ n` does not move between days `n` and `n + 1`.
Source: mandate K3 (`Degenerate`); [[STANDARDS]] §3; this run (repair r2)
Kind: L
Fidelity: n/a -/
theorem pointMass_degOne_degenerate_iff (rep : ℕ → ℕ → ℚ) (χ : ℕ → ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁)) :
    Degenerate (stateOf (fixedCF rep)) (pointMass v) (degOne χ) ↔
      ∀ n, halfRound (n + 1)
          (marketValue 𝗜𝚺₁ (Nat.pair (n + 1) (Encodable.encode (sentenceOfCode (χ n))))) =
        halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode (χ n))))) := by
  unfold Degenerate
  refine forall_congr' fun n => ?_
  show v.payout (stateOf (fixedCF rep) (n + 1) (degOne χ n)) = 1 ↔ _
  unfold degOne
  rw [payout_stateOf_oneTable rep v hv]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h0 => absurd h0 zero_ne_one, fun hh => absurd hh h⟩

/-- **The one-coordinate package with the point mass as base is inhabited iff the family's
rounded price never moves** — the no-move regime at the superbelief side, exactly. `PCPσ`,
`E5σ` and `E1x (pointMass v) (pointMass v)` hold unconditionally; `Degenerate` is the no-move
condition. **Base = the superbelief itself**, not the LIA: this says nothing about
`no_degenerate_linked_bli_LIA_oneCoord`'s package (which is empty,
`LiaPackage.not_lia_small_coherent_mixture_exists`, repair r3). It also shows the point-mass base is the
wrong place to look for the theorem's content: one move on one day already empties this
package, while the theorem needs infinitely many.
Source: [[STANDARDS]] §3 (artifact check, at the superbelief side only); audit r2 B1 (both lenses); this run (repair r2)
Kind: N-
Fidelity: n/a (point mass; `P = Q`; the base is not the LIA)
Hyps: (a) -/
theorem pointMass_oneCoord_package_iff_still (rep : ℕ → ℕ → ℚ) (χ : ℕ → ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁)) :
    (PCPσ (stateAtoms (stateOf (fixedCF rep)) (oneSystem χ rep)) (paperDP 𝗜𝚺₁) (pointMass v) ∧
      E5σ (stateOf (fixedCF rep)) (oneSystem χ rep) (pointMass v) ∧
      E1x (pointMass v) (pointMass v) ∧
      Degenerate (stateOf (fixedCF rep)) (pointMass v) (degOne χ)) ↔
    ∀ n, halfRound (n + 1)
        (marketValue 𝗜𝚺₁ (Nat.pair (n + 1) (Encodable.encode (sentenceOfCode (χ n))))) =
      halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode (χ n))))) := by
  rw [← pointMass_degOne_degenerate_iff rep χ v hv]
  exact ⟨fun h => h.2.2.2, fun h =>
    ⟨pointMass_pcpσ v hv _, pointMass_oneSystem_e5σ rep χ v hv, pointMass_e1x v, h⟩⟩

end Cleanroom.Bli.BliLinkage
