import Cleanroom.Bli.BliFound.StateSentence

/-!
# `bli-found` · Grid: what the B2 cells can force, a market-independent candidate grid, and the
`RoundsOf` tie for the B2 system

Added in repair round 2 (after audit round 2). Three things the round-2 audits asked for or
proposed, each lifted from an auditor's probe where one existed:

* **The B2 state sentence is never a fresh atom** (`stateSentence_ne_stateAtom`; adversarial
  N1, probe P1): `⊤` or a `⋏`, never `Formula.atom _`. So the main-body predicates of
  `Constraints.lean`, which condition on `stateAtom m q`, say nothing about B2; the σ-parametric
  forms `Constraints.E2xσ` etc. exist for that.
* **What the cells of `LNKcell_stateSentence` can force** (adversarial N2, probes P2/P3):
  at the vacuous cell `(-1, 2)` the linkage is a tautology for every state-sentence family
  (`lnkcell_default_cell_tautology`), and any cell bounds meeting `hcell` for `halfRound` overlap
  on a nonempty open interval below `1/2` (`hcell_forces_overlap`) — a structural consequence of
  FAF's `PCWorld.ValuesAt` being undetermined at the threshold: a forced interval quote must be
  strictly open around every price of the cell, and open supersets of adjacent rounding cells
  overlap. Findings F-16.
* **A market-independent candidate grid** for the T7 witness (fidelity §3.1, adversarial N3,
  probe P4): the four tables over `[⌜⊥⌝, ⌜⊤⌝]` with indices in `{0, 1}`, fixed before the market
  is consulted; the actual rounded table is one of them (`actualCode_mem_fixedStates`), and
  **exactly the actual one holds** in every completed-theory world of `paperDP 𝗜𝚺₁`
  (`fixedStates_decided`). `StateSentence.witnessStates` defines its second candidate *from* the
  market's rounded quotes, so "the market decides" was definitional there; here the grid does not
  mention the market and the market's rounded quotes of `⊥` and `⊤` select one pre-listed table.
* **The `RoundsOf` tie for the B2 system** (adversarial N7): `Constraints.RoundsOf` takes a real
  rounding `D : ℕ → ℝ → ℝ`, the B2 construction a rational `round : ℕ → ℚ → ℕ` with
  representatives `rep`. `b2StateSystem_val_actual` gives the value of the actual table on a
  listed sentence in closed form, and `b2StateSystem_roundsOf` the tie
  `RoundsOf (b2StateSystem …) (liaHistory (paperDP T)) (fun m x => rep m (round m (ratOfReal x)))`
  whenever the index list covers the day's small sentences — the hypothesis a dependent
  discharges once it has a computable enumeration of `smallSet` (stretch S1). No instance here:
  the witness index `[⌜⊥⌝, ⌜⊤⌝]` covers `smallSet m` only at `m = 0`.

Sources: audit r2 (fidelity §3.1, adversarial N1/N2/N3/N7); mandate T7 (witness); bli-paper-034/038.
-/

namespace Cleanroom.Bli.BliFound

open LogicalInduction LO.Propositional

section NotAnAtom

/-- A finite conjunction (`⊤` or `_ ⋏ _`) is never an atom.
Source: none: infrastructure; audit r2 (adversarial N1, probe P1)
Kind: L
Fidelity: n/a -/
lemma conjList_ne_atom (c : ℕ) : ∀ l : List Sentence, conjList l ≠ Formula.atom c
  | [] => by
      intro h
      change (⊥ : Sentence) 🡒 ⊥ = Formula.atom c at h
      cases h
  | _ :: _ => by
      intro h
      change Formula.and _ _ = Formula.atom c at h
      cases h

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]

/-- **The B2 state sentence is not a fresh atom** (it is `⊤` or a conjunction of tag-`2`
literals), for every theory, rounding, day and code. Hence `Constraints.E2x S P`, `E3 S P`,
`E4 S P`, `E5 S P`, `TB S P` — all stated over `stateAtom m q` — say nothing about
`stateSentence T round m q`, even on `b2StateSystem`; the σ-parametric forms are for that.
Source: audit r2 (adversarial N1, probe P1)
Kind: L
Fidelity: exact -/
theorem stateSentence_ne_stateAtom (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (m q m' q' : ℕ) :
    stateSentence T round hround m q ≠ stateAtom m' q' := by
  unfold stateSentence stateAtom freshAtom
  exact conjList_ne_atom _ _

end NotAnAtom

section Cells

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]

/-- **`LNKcell` at the vacuous cell `(-1, 2)` holds for every state-sentence family and every
state system** over `paperDP T`: the antecedent is never used (`quoteAt_default_cell`). The
content of `LNKcell_stateSentence` is therefore exactly how tight the dependent's cells are.
Source: audit r2 (adversarial N2, probe P2)
Kind: L
Fidelity: n/a -/
theorem lnkcell_default_cell_tautology (σ : ℕ → ℕ → Sentence) (S : StateSystem) :
    LNKcell σ (quoteAt T) S (fun _ _ _ => ((-1 : ℚ), (2 : ℚ))) (paperDP T) :=
  fun m _ _ φ _ v hv _ => quoteAt_default_cell T m φ v hv

/-- **Legitimate cells for `halfRound` must overlap.** Any cell bounds satisfying
`LNKcell_stateSentence`'s `hcell` for `halfRound` have `cellLo m 0 < 0`, `1/2 ≤ cellHi m 0`,
`cellLo m 1 < 1/2` and `1 < cellHi m 1`; so the cells of indices `0` and `1` both contain the
nonempty open interval `(max (cellLo m 0) (cellLo m 1), 1/2)`, and the interval quote forced when
the state says index `1` never excludes prices that `halfRound` sends to `0`. Structural: FAF's
`PCWorld.ValuesAt` fixes `⌜X > r⌝` only off `r = x`, so a forced quote is strictly open around
the price, and open supersets of adjacent half-open rounding cells overlap. `hcell` cannot be met
by a partition. (Findings F-16.)
Source: audit r2 (adversarial N2, probe P3); FAF `PCWorld.ValuesAt`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem hcell_forces_overlap (cellLo cellHi : ℕ → ℕ → ℚ)
    (hcell : ∀ m (x : ℚ) r, 0 ≤ x → x ≤ 1 → halfRound m x = r → cellLo m r < x ∧ x < cellHi m r)
    (m : ℕ) :
    cellLo m 0 < 0 ∧ (1 / 2 : ℚ) ≤ cellHi m 0 ∧ cellLo m 1 < 1 / 2 ∧ 1 < cellHi m 1 := by
  have h0 := hcell m 0 0 le_rfl (by norm_num) (by norm_num [halfRound])
  have h1 := hcell m 1 1 (by norm_num) le_rfl (by norm_num [halfRound])
  have hhalf := hcell m (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num [halfRound])
  refine ⟨h0.1, ?_, hhalf.1, h1.2⟩
  by_contra hcon
  rw [not_le] at hcon
  set x : ℚ := (max (cellHi m 0) 0 + 1 / 2) / 2 with hx
  have hmax0 : (0 : ℚ) ≤ max (cellHi m 0) 0 := le_max_right _ _
  have hmax1 : cellHi m 0 ≤ max (cellHi m 0) 0 := le_max_left _ _
  have hmaxlt : max (cellHi m 0) 0 < 1 / 2 := max_lt hcon (by norm_num)
  have hx0 : 0 ≤ x := by rw [hx]; linarith
  have hxlt : x < 1 / 2 := by rw [hx]; linarith
  have hr : halfRound m x = 0 := by unfold halfRound; rw [if_pos hxlt]
  have := (hcell m x 0 hx0 (by linarith) hr).2
  rw [hx] at this
  linarith

/-- The witness's own cells (`halfLo`/`halfHi`: `(-1, 1/2)` and `(1/4, 2)`) are an instance of
the overlap: both contain `(1/4, 1/2)`. -/
example (m : ℕ) : halfLo m 0 < 0 ∧ (1 / 2 : ℚ) ≤ halfHi m 0 ∧ halfLo m 1 < 1 / 2 ∧ 1 < halfHi m 1 :=
  hcell_forces_overlap halfLo halfHi halfRound_cell m

end Cells

section FixedGrid

/-! ## A market-independent four-table grid for the T7 witness -/

/-- The two-entry table over `[⌜⊥⌝, ⌜⊤⌝]` with grid indices `a`, `b`.
Source: audit r2 (adversarial N3, probe P4)
Kind: D
Fidelity: n/a -/
def tbl (a b : ℕ) : List (ℕ × ℕ) :=
  [(Encodable.encode (⊥ : Sentence), a), (Encodable.encode (⊤ : Sentence), b)]

/-- The market's rounded quote of `⊥` on day `m` (at `𝗜𝚺₁`, with `halfRound`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def roundedBot (m : ℕ) : ℕ :=
  halfRound m (marketValue 𝗜𝚺₁ (Nat.pair m (Encodable.encode (⊥ : Sentence))))

/-- The market's rounded quote of `⊤` on day `m`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def roundedTop (m : ℕ) : ℕ :=
  halfRound m (marketValue 𝗜𝚺₁ (Nat.pair m (Encodable.encode (⊤ : Sentence))))

/-- The package's actual table is `tbl (roundedBot m) (roundedTop m)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma actualTable_eq_tbl (m : ℕ) :
    actualTable 𝗜𝚺₁ halfRound witnessIndex m = tbl (roundedBot m) (roundedTop m) := rfl

/-- **The four fixed tables** the two-cell rounding can write out over `[⌜⊥⌝, ⌜⊤⌝]` — the same
list on every day, defined without reference to the market.
Source: mandate T7 (witness); bli-paper-038; audit r2 (fidelity §3.1, adversarial N3, probe P4)
Kind: D
Fidelity: n/a -/
def fixedStates (_m : ℕ) : Finset ℕ :=
  {Encodable.encode (tbl 0 0), Encodable.encode (tbl 0 1),
    Encodable.encode (tbl 1 0), Encodable.encode (tbl 1 1)}

/-- `tbl_inj`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tbl_inj {a b a' b' : ℕ} : tbl a b = tbl a' b' ↔ a = a' ∧ b = b' := by
  simp [tbl]

/-- A fixed table's entries are the rounded quotes iff its indices are the rounded quotes.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_tbl (m a b : ℕ) :
    (∀ e ∈ tbl a b, halfRound m (marketValue 𝗜𝚺₁ (Nat.pair m e.1)) = e.2) ↔
      (roundedBot m = a ∧ roundedTop m = b) := by
  simp [tbl, roundedBot, roundedTop]

/-- **The actual rounded table is one of the four** (`halfRound` only produces `0` and `1`).
Source: mandate T7 (witness); audit r2 (adversarial N3, probe P4)
Kind: L
Fidelity: exact -/
theorem actualCode_mem_fixedStates (m : ℕ) :
    actualCode 𝗜𝚺₁ halfRound witnessIndex m ∈ fixedStates m := by
  unfold actualCode
  rw [actualTable_eq_tbl]
  have h0 : roundedBot m ≤ 1 := halfRound_le_one _ _
  have h1 : roundedTop m ≤ 1 := halfRound_le_one _ _
  simp only [fixedStates, Finset.mem_insert, Finset.mem_singleton]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h0 with ha | ha <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with hb | hb <;>
  simp [ha, hb]

/-- The grid has four candidates.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fixedStates_card (m : ℕ) : (fixedStates m).card = 4 := by
  simp [fixedStates, tbl]

/-- **N+ (T7): exactly one of four pre-listed tables holds.** In every completed-theory world of
`paperDP 𝗜𝚺₁`, a candidate `q ∈ fixedStates m` has its state sentence hold iff `q` is the actual
rounded table: the market's rounded quotes of `⊥` and `⊤` select one of four tables fixed before
the market is consulted. This is `StateSentence.witnessStates_decided` over a grid that does not
mention the market — bli-paper-038's exclusivity over a real candidate grid.
Source: mandate T7 (witness); bli-paper-038; audit r2 (fidelity §3.1, adversarial N3, probe P4)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem fixedStates_decided (m : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁)) :
    ∀ q ∈ fixedStates m,
      (v.Holds (stateSentence 𝗜𝚺₁ halfRound halfRound_computable m q) ↔
        q = actualCode 𝗜𝚺₁ halfRound witnessIndex m) := by
  intro q hq
  rw [stateSentence_reflected 𝗜𝚺₁ halfRound halfRound_computable m q v hv]
  unfold actualCode
  rw [actualTable_eq_tbl]
  simp only [fixedStates, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl <;>
  · rw [tableOfCode_encode, holds_tbl, Encodable.encode_inj, tbl_inj]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩

/-- The fixed grid as a B2 state system at `𝗜𝚺₁` (representatives as in `witnessSystem`).
Source: mandate T7 (witness); audit r2 (adversarial N3)
Kind: D
Fidelity: n/a -/
noncomputable def fixedSystem : StateSystem :=
  b2StateSystem 𝗜𝚺₁ halfRound witnessIndex fixedStates actualCode_mem_fixedStates witnessRep

/-- **N+ (T7): linkage on the fixed grid.** `LNKcell` for the B2 state sentence over
`paperDP 𝗜𝚺₁` on the four-table system.
Source: mandate T7 (witness); audit r2 (adversarial N3)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem LNKcell_fixedSystem :
    LNKcell (stateSentence 𝗜𝚺₁ halfRound halfRound_computable) (quoteAt 𝗜𝚺₁) fixedSystem
      (cellOfTable halfLo halfHi) (paperDP 𝗜𝚺₁) :=
  LNKcell_stateSentence 𝗜𝚺₁ halfRound halfRound_computable witnessIndex fixedStates
    actualCode_mem_fixedStates witnessRep halfLo halfHi halfRound_cell

end FixedGrid

section RoundsOfTie

/-! ## The `RoundsOf` tie for the B2 system (audit r2 adversarial N7) -/

/-- `entryOf` on a keyed map `c ↦ (c, f c)`: the first (and only) entry at `c`, if `c` is listed.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma entryOf_map_self (f : ℕ → ℕ) (c : ℕ) : ∀ l : List ℕ,
    entryOf c (l.map fun c => (c, f c)) = if c ∈ l then some (f c) else none
  | [] => by simp [entryOf]
  | x :: l => by
      by_cases hx : x = c
      · subst hx
        simp [entryOf]
      · have ih := entryOf_map_self f c l
        simp only [List.map_cons, entryOf, hx, if_false, ih, List.mem_cons]
        by_cases hc : c ∈ l
        · simp [hc]
        · simp [hc, Ne.symm hx]

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]

omit [𝗥₀ ⪯ T] in
/-- The actual table's entry at a listed code is the rounded quote of that code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma entryOf_actualTable (round : ℕ → ℚ → ℕ) (index : ℕ → List ℕ) (m c : ℕ)
    (hc : c ∈ index m) :
    entryOf c (actualTable T round index m) = some (round m (marketValue T (Nat.pair m c))) := by
  unfold actualTable
  rw [entryOf_map_self, if_pos hc]

omit [𝗥₀ ⪯ T] in
/-- **The B2 system's value of the actual table on a listed sentence, in closed form**:
`rep m (round m (𝑸_m(φ)))`, the representative of the rounded exact quote.
Source: bli-paper-034 (`D_n(𝑸_n(φ))`); audit r2 (adversarial N7)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem b2StateSystem_val_actual (round : ℕ → ℚ → ℕ) (index : ℕ → List ℕ)
    (states : ℕ → Finset ℕ) (hact : ∀ m, actualCode T round index m ∈ states m)
    (rep : ℕ → ℕ → ℚ) (m : ℕ) (φ : Sentence) (hφ : Encodable.encode φ ∈ index m) :
    (b2StateSystem T round index states hact rep).val m
        ((b2StateSystem T round index states hact rep).actual m) φ =
      ((rep m (round m (paperQuote T m (Encodable.encode φ))) : ℚ) : ℝ) := by
  simp only [b2StateSystem, actualCode, tableOfCode_encode]
  rw [entryOf_actualTable T round index m _ hφ]
  simp

/-- A classical left inverse of the cast `ℚ → ℝ` (`0` off the rationals), so that a rational
rounding can be handed to `Constraints.RoundsOf`, whose rounding is real-valued.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def ratOfReal (x : ℝ) : ℚ :=
  open Classical in if h : ∃ q : ℚ, (q : ℝ) = x then h.choose else 0

/-- `ratOfReal_cast`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ratOfReal_cast (q : ℚ) : ratOfReal (q : ℝ) = q := by
  unfold ratOfReal
  have h : ∃ q' : ℚ, (q' : ℝ) = (q : ℝ) := ⟨q, rfl⟩
  rw [dif_pos h]
  exact Rat.cast_injective h.choose_spec

/-- **The B2 system writes out the paper market** (`RoundsOf`, the tie `IsBLI_AppB` leaves
implicit), whenever the index list covers the day's small sentences: with
`D m x := rep m (round m (ratOfReal x))`, `S.val m (S.actual m) φ = D m (liaHistory (paperDP T) m φ)`
for every `φ ∈ smallSet m`. The covering hypothesis is what a dependent discharges from a
computable enumeration of `smallSet` (stretch S1); no instance is shipped here (the witness index
`[⌜⊥⌝, ⌜⊤⌝]` covers `smallSet m` only at `m = 0`).
Source: bli-paper-034; Appendix B (`main.tex:431`); audit r2 (adversarial N7)
Kind: C
Fidelity: exact
Hyps: (a); `hindex` is the index-coverage condition on the dependent's data -/
theorem b2StateSystem_roundsOf (round : ℕ → ℚ → ℕ) (index : ℕ → List ℕ)
    (states : ℕ → Finset ℕ) (hact : ∀ m, actualCode T round index m ∈ states m)
    (rep : ℕ → ℕ → ℚ) (hindex : ∀ m, ∀ φ ∈ smallSet m, Encodable.encode φ ∈ index m) :
    RoundsOf (b2StateSystem T round index states hact rep) (liaHistory (paperDP T))
      (fun m x => ((rep m (round m (ratOfReal x)) : ℚ) : ℝ)) := by
  intro m φ hφ
  rw [b2StateSystem_val_actual T round index states hact rep m φ (hindex m φ hφ),
    paperQuote_eq_liaHistory]
  dsimp only
  rw [ratOfReal_cast]

end RoundsOfTie

end Cleanroom.Bli.BliFound
