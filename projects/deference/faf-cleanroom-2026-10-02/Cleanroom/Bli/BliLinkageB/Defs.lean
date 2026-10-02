import Cleanroom.Bli.BliTrajectory.Defs

/-!
# bli-linkage, angle B — definitions of record (interval linkage)

Angle B of the dual package `bli-linkage` takes the linkage `bli-found` actually proved for the
B2 state sentence: `LNKcell_stateSentence` forces, in every completed-theory world, the
*interval quote* of each listed coordinate for an **open neighbourhood** of its rounding cell
(findings F-16: legitimate cells overlap, `Grid.hcell_forces_overlap`). This module fixes the
objects every theorem of the angle is stated over.

* **Coherence over a class of worlds.** `CoherentOnW 𝒲 A p` is `bli-found`'s `CoherentOn`
  with the world class a parameter: `CoherentOn D A p = CoherentOnW (ConsistentWith D) A p`
  definitionally, and `CoherentOnTheory DP A p` is the completed-theory class. The
  σ-parametric coherence `bli-found` F-17 left to this package comes in both forms (`PCPσ`,
  stage-relative; `PCPσTheory`, theory-relative), parametric in the extra atom set.
* **Interval semantics at the world level.** `IntervalSem quote v` is what a single world
  must satisfy for interval quotes to behave like "the price is in the interval":
  monotone under strict enlargement, and two held quotes have meeting closed intervals.
  An `IntervalFamily DP` (quote family + the price it is about, with the two reflection
  lemmas of `StateSentence.quoteAt` as fields) gives `IntervalSem` in every completed-theory
  world. The B2 instance is `InstanceB2.intervalFamilyB2`.
* **Linkage at the world level.** `LinkedWorld σ quote S cellOf m v`: in `v`, the state
  sentence of every candidate forces the quote of the cell it assigns. `LNKcell` is exactly
  "every completed-theory world is linked" (`lnkcell_iff_linkedWorld`).
* **The cell-literal objects shared with angle A** (`CellFamily`, `stateOf`, `pinned`,
  `cellMass`, `D_NNUcell`, `Degenerate`), with the *same* `D_NNUcell` statement so the
  reconciler can diff. `CellFamily` is parametric in a world class `𝒲` for its
  exclusivity/exhaustiveness fields; `CellFamilyT DP` is the mandate's completed-theory form.
* **Two conditions the stage-level determination theorem needs** (`Determination.lean`):
  `SpuriousEntails` (a candidate together with a cell literal it does not list entails another
  candidate — true of full product grids, and of `Grid.fixedStates`) and `ValuesAtRep` (every
  candidate lists every indexed coordinate with a legitimate cell and values it at the
  representative — the B2 system's `val`, discharged by `rfl`-level reasoning).

Nothing here is a headline: every declaration is `D` or `L`.
-/

namespace Cleanroom.Bli.BliLinkageB

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

/-! ## Coherence over a class of worlds -/

/-- **Coherence on a finite Boolean algebra, relative to a class of worlds.** `p` is a convex
combination of the payouts of finitely many worlds of the class `𝒲`, on every sentence whose
atoms lie in `A`. `bli-found`'s `CoherentOn D A p` is the instance `𝒲 := ConsistentWith D`
(`coherentOn_iff_coherentOnW`, definitional).
Source: bli-slides-003/011; [[bli-program]] §2.6; bli-found `Constraints.CoherentOn`
Kind: D
Fidelity: exact (the world class is a parameter) -/
def CoherentOnW (𝒲 : PCWorld → Prop) (A : Finset ℕ) (p : Sentence → ℝ) : Prop :=
  ∃ (k : ℕ) (W : Fin k → PCWorld) (w : Fin k → ℝ),
    (∀ i, 𝒲 (W i)) ∧ (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
    ∀ φ, sentenceAtomCodes φ ⊆ A → p φ = ∑ i, w i * (W i).payout φ

/-- `CoherentOn D A p` is coherence over the worlds consistent with the stage `D`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem coherentOn_iff_coherentOnW (D : Finset Sentence) (A : Finset ℕ) (p : Sentence → ℝ) :
    CoherentOn D A p ↔ CoherentOnW (fun v => v.ConsistentWith D) A p := Iff.rfl

/-- Coherence is monotone in the world class.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem CoherentOnW.mono {𝒲 𝒲' : PCWorld → Prop} (h : ∀ v, 𝒲 v → 𝒲' v) {A : Finset ℕ}
    {p : Sentence → ℝ} (hc : CoherentOnW 𝒲 A p) : CoherentOnW 𝒲' A p := by
  obtain ⟨k, W, w, hW, hw, hsum, hrep⟩ := hc
  exact ⟨k, W, w, fun i => h _ (hW i), hw, hsum, hrep⟩

/-- Coherence is antitone in the atom set.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem CoherentOnW.anti {𝒲 : PCWorld → Prop} {A A' : Finset ℕ} (h : A' ⊆ A)
    {p : Sentence → ℝ} (hc : CoherentOnW 𝒲 A p) : CoherentOnW 𝒲 A' p := by
  obtain ⟨k, W, w, hW, hw, hsum, hrep⟩ := hc
  exact ⟨k, W, w, hW, hw, hsum, fun φ hφ => hrep φ (hφ.trans h)⟩

/-- **Coherence relative to the completed theory**: a mixture of worlds consistent with every
stage of `DP`. Stronger than `CoherentOn (DP.D n)` for every `n` (`CoherentOnTheory.coherentOn`).
Source: [[bli-program]] §2.6; mandate § Definitions (`CoherentOnTheory`)
Kind: D
Fidelity: exact -/
def CoherentOnTheory (DP : DeductiveProcess) (A : Finset ℕ) (p : Sentence → ℝ) : Prop :=
  CoherentOnW (fun v => v.ConsistentWithTheory DP) A p

/-- Theory-relative coherence implies stage-relative coherence at every stage.
Source: mandate § Definitions (`PCPσTheory → PCPσ`)
Kind: L
Fidelity: n/a -/
theorem CoherentOnTheory.coherentOn {DP : DeductiveProcess} {A : Finset ℕ} {p : Sentence → ℝ}
    (h : CoherentOnTheory DP A p) (n : ℕ) : CoherentOn (DP.D n) A p :=
  (coherentOn_iff_coherentOnW _ _ _).2 (h.mono fun _ hv => hv n)

/-- The atom codes of the day-`n` small sentences.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def smallAtoms (n : ℕ) : Finset ℕ := (smallSet n).biUnion sentenceAtomCodes

/-- The atom codes of the day-`(n+1)` state sentences of the candidates.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def stateAtoms (σ : ℕ → ℕ → Sentence) (S : StateSystem) (n : ℕ) : Finset ℕ :=
  (S.states (n + 1)).biUnion fun q => sentenceAtomCodes (σ (n + 1) q)

/-- A small sentence's atoms lie in `smallAtoms n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem atoms_subset_smallAtoms {n : ℕ} {φ : Sentence} (h : φ ∈ smallSet n) :
    sentenceAtomCodes φ ⊆ smallAtoms n :=
  Finset.subset_biUnion_of_mem sentenceAtomCodes h

/-- A day-`(n+1)` candidate's state sentence has its atoms in `stateAtoms σ S n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem atoms_subset_stateAtoms (σ : ℕ → ℕ → Sentence) (S : StateSystem) {n q : ℕ}
    (h : q ∈ S.states (n + 1)) : sentenceAtomCodes (σ (n + 1) q) ⊆ stateAtoms σ S n :=
  Finset.subset_biUnion_of_mem (fun q => sentenceAtomCodes (σ (n + 1) q)) h

/-- **PCPσ — σ-parametric finite coherence of `P_n`, stage-relative**: on every day `n`, `P n`
is a mixture of worlds consistent with the stage `DP.D n`, on the algebra generated by the
day-`n` small sentences and the extra atoms `atoms n` (a parameter; the theorems ask
`stateAtoms σ S n ⊆ atoms n`). The σ-parametric coherence `bli-found` F-17 left to this package.
Source: [[bli-program]] §2.6; mandate § Definitions (`PCPσ`); bli-found F-17
Kind: D
Fidelity: exact -/
def PCPσ (atoms : ℕ → Finset ℕ) (DP : DeductiveProcess) (P : History) : Prop :=
  ∀ n, CoherentOn (DP.D n) (smallAtoms n ∪ atoms n) (P n)

/-- **PCPσTheory — the same, relative to the completed theory**: every world of the mixture is
consistent with *every* stage of `DP`. The linkage `LNKcell` is a completed-theory fact, so
this is the form under which linkage can be applied to the worlds of the mixture
(`Bracket.lean`); the price is that completed-theory worlds have every quote decided
(`Determination.theory_coherent_e1x_decides`).
Source: mandate § Definitions (`PCPσTheory`); K4
Kind: D
Fidelity: exact -/
def PCPσTheory (atoms : ℕ → Finset ℕ) (DP : DeductiveProcess) (P : History) : Prop :=
  ∀ n, CoherentOnTheory DP (smallAtoms n ∪ atoms n) (P n)

/-- `PCPσTheory → PCPσ`.
Source: mandate § Definitions
Kind: L
Fidelity: n/a -/
theorem PCPσTheory.toPCPσ {atoms : ℕ → Finset ℕ} {DP : DeductiveProcess} {P : History}
    (h : PCPσTheory atoms DP P) : PCPσ atoms DP P :=
  fun n => (h n).coherentOn n

/-! ## Interval semantics and linkage at the world level -/

/-- **Interval semantics in one world**: the quotes of a sentence behave like "`𝑸_m(φ)` lies in
the interval": (`mono`) a held quote stays held under strict enlargement of the interval;
(`meet`) two held quotes of the same coordinate have meeting closed intervals. Every
completed-theory world of an `IntervalFamily` satisfies it (`IntervalFamily.intervalSem`); a
world of a *stage* mixture need not, which is why the bracket theorems take it as a hypothesis
on the mixture's worlds.
Source: mandate § Attempt angles (B); bli-found `StateSentence.holds_quoteAt_of_lt_of_lt`/`le_of_holds_quoteAt`
Kind: D
Fidelity: exact -/
structure IntervalSem (quote : ℕ → Sentence → ℚ → ℚ → Sentence) (v : PCWorld) : Prop where
  /-- Strict enlargement preserves a held quote. -/
  mono : ∀ (m : ℕ) (φ : Sentence) (lo hi lo' hi' : ℚ), lo' < lo → hi < hi' →
    v.Holds (quote m φ lo hi) → v.Holds (quote m φ lo' hi')
  /-- Two held quotes of one coordinate have meeting closed intervals. -/
  meet : ∀ (m : ℕ) (φ : Sentence) (lo hi lo' hi' : ℚ),
    v.Holds (quote m φ lo hi) → v.Holds (quote m φ lo' hi') → max lo lo' ≤ min hi hi'

/-- **An interval-quote family of record**: the quote sentences, the price they are about, and
the two reflection facts in every completed-theory world of `DP` — the shape of
`StateSentence.holds_quoteAt_of_lt_of_lt` / `le_of_holds_quoteAt`. The B2 instance over
`paperDP T` is `InstanceB2.intervalFamilyB2`.
Source: mandate § Definitions (angle B: `IntervalFamily`)
Kind: D
Fidelity: exact -/
structure IntervalFamily (DP : DeductiveProcess) where
  /-- The interval quote "`lo < 𝑸_m(φ) ≤ hi`". -/
  quote : ℕ → Sentence → ℚ → ℚ → Sentence
  /-- The exact price the quote is about. -/
  price : ℕ → Sentence → ℚ
  /-- A strictly containing interval's quote holds in every completed-theory world. -/
  reflect_lt : ∀ (m : ℕ) (φ : Sentence) (lo hi : ℚ), lo < price m φ → price m φ < hi →
    ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (quote m φ lo hi)
  /-- A held quote's closed interval contains the price, in every completed-theory world. -/
  le_of_holds : ∀ (m : ℕ) (φ : Sentence) (lo hi : ℚ) (v : PCWorld), v.ConsistentWithTheory DP →
    v.Holds (quote m φ lo hi) → lo ≤ price m φ ∧ price m φ ≤ hi

/-- Every completed-theory world of an interval family has interval semantics.
Source: mandate § Attempt angles (B)
Kind: L
Fidelity: n/a -/
theorem IntervalFamily.intervalSem {DP : DeductiveProcess} (F : IntervalFamily DP) (v : PCWorld)
    (hv : v.ConsistentWithTheory DP) : IntervalSem F.quote v where
  mono := by
    intro m φ lo hi lo' hi' hlo hhi h
    obtain ⟨h1, h2⟩ := F.le_of_holds m φ lo hi v hv h
    exact F.reflect_lt m φ lo' hi' (lt_of_lt_of_le hlo h1) (lt_of_le_of_lt h2 hhi) v hv
  meet := by
    intro m φ lo hi lo' hi' h h'
    obtain ⟨h1, h2⟩ := F.le_of_holds m φ lo hi v hv h
    obtain ⟨h1', h2'⟩ := F.le_of_holds m φ lo' hi' v hv h'
    exact le_trans (max_le h1 h1') (le_min h2 h2')

/-- In a completed-theory world, a quote is decided by the price: held when the price is
strictly inside, refuted when the price is strictly outside the closed interval.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IntervalFamily.not_holds_of_lt {DP : DeductiveProcess} (F : IntervalFamily DP)
    {m : ℕ} {φ : Sentence} {lo hi : ℚ} (v : PCWorld) (hv : v.ConsistentWithTheory DP)
    (h : F.price m φ < lo ∨ hi < F.price m φ) : ¬ v.Holds (F.quote m φ lo hi) := by
  intro hq
  obtain ⟨h1, h2⟩ := F.le_of_holds m φ lo hi v hv hq
  rcases h with h | h
  · exact absurd (lt_of_lt_of_le h h1) (lt_irrefl _)
  · exact absurd (lt_of_le_of_lt h2 h) (lt_irrefl _)

/-- **Linkage in one world**: the state sentence of every day-`m` candidate forces the interval
quote of every day-`m` small sentence for the cell the candidate assigns it. `LNKcell` is
"every completed-theory world is linked on every day" (`lnkcell_iff_linkedWorld`).
Source: bli-found `StateSentence.LNKcell`; mandate § Attempt angles (B)
Kind: D
Fidelity: exact -/
def LinkedWorld (σ : ℕ → ℕ → Sentence) (quote : ℕ → Sentence → ℚ → ℚ → Sentence)
    (S : StateSystem) (cellOf : ℕ → ℕ → Sentence → ℚ × ℚ) (m : ℕ) (v : PCWorld) : Prop :=
  ∀ q ∈ S.states m, ∀ φ ∈ smallSet m, v.Holds (σ m q) →
    v.Holds (quote m φ (cellOf m q φ).1 (cellOf m q φ).2)

/-- `LNKcell` is linkage of every completed-theory world on every day.
Source: bli-found `StateSentence.LNKcell`
Kind: L
Fidelity: n/a -/
theorem lnkcell_iff_linkedWorld (σ : ℕ → ℕ → Sentence) (quote : ℕ → Sentence → ℚ → ℚ → Sentence)
    (S : StateSystem) (cellOf : ℕ → ℕ → Sentence → ℚ × ℚ) (DP : DeductiveProcess) :
    LNKcell σ quote S cellOf DP ↔
      ∀ m (v : PCWorld), v.ConsistentWithTheory DP → LinkedWorld σ quote S cellOf m v := by
  constructor
  · intro h m v hv q hq φ hφ hs
    exact h m q hq φ hφ v hv hs
  · intro h m q hq φ hφ v hv hs
    exact h m v hv q hq φ hφ hs

/-! ## The cell-literal objects (shared with angle A) -/

/-- **An abstract cell-literal family**: the literal "`round_m(𝑸_m(φ)) = r`", the grid indices of
day `m`, a representative per cell, and exclusivity/exhaustiveness of the literals in every
world of the class `𝒲`. The mandate's form has `𝒲 := ConsistentWithTheory DP` (`CellFamilyT`);
the class is a parameter so that the *stage-level* theorems can say exactly which world facts
they use (none: `Determination.determination_stage` needs neither field). B2 instance:
`InstanceB2.cellFamilyB2`.
Source: mandate § Definitions (`CellFamily`); bli-found `StateSentence.cellSentence_reflected`
Kind: D
Fidelity: exact (abstract; the world class is a parameter) -/
structure CellFamily (𝒲 : PCWorld → Prop) where
  /-- The cell literal `literal m φ r` (the mandate's `lit`; `lit` is a reserved token here). -/
  literal : ℕ → Sentence → ℕ → Sentence
  /-- The grid indices on day `m`. -/
  cells : ℕ → Finset ℕ
  /-- The representative of cell `r` on day `m`. -/
  rep : ℕ → ℕ → ℚ
  /-- Distinct literals of one coordinate never both hold in a world of the class. -/
  excl : ∀ (m : ℕ) (φ : Sentence) (r r' : ℕ), r ≠ r' → ∀ v : PCWorld, 𝒲 v →
    ¬ (v.Holds (literal m φ r) ∧ v.Holds (literal m φ r'))
  /-- Some literal of each coordinate holds in every world of the class. -/
  exh : ∀ (m : ℕ) (φ : Sentence), ∀ v : PCWorld, 𝒲 v → ∃ r ∈ cells m, v.Holds (literal m φ r)

/-- The mandate's cell family: exclusivity and exhaustiveness in every completed-theory world.
Source: mandate § Definitions (`CellFamily`)
Kind: D
Fidelity: exact -/
abbrev CellFamilyT (DP : DeductiveProcess) := CellFamily fun v => v.ConsistentWithTheory DP

/-- **The linked state sentence over an abstract cell family**: the conjunction of the literals
`lit m (sentenceOfCode c) r` over the entries `(c, r)` of the table with code `q`. At B2 it is
definitionally `StateSentence.stateSentence` (`InstanceB2.stateOf_eq_stateSentence`).
Source: mandate § Definitions (`stateOf`); bli-found `StateSentence.stateSentence`
Kind: D
Fidelity: exact -/
def stateOf {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) (m q : ℕ) : Sentence :=
  conjList ((tableOfCode q).map fun e => C.literal m (sentenceOfCode e.1) e.2)

/-- A world holds `stateOf C m q` iff it holds the literal of every entry of the table.
Source: none: infrastructure (bli-found `holds_conjList`)
Kind: L
Fidelity: n/a -/
theorem holds_stateOf {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) (m q : ℕ) (v : PCWorld) :
    v.Holds (stateOf C m q) ↔
      ∀ e ∈ tableOfCode q, v.Holds (C.literal m (sentenceOfCode e.1) e.2) := by
  unfold stateOf
  rw [holds_conjList]
  constructor
  · intro h e he
    exact h _ (List.mem_map.2 ⟨e, he, rfl⟩)
  · intro h ψ hψ
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hψ
    exact h e he

/-- **Linkage is propositional**: the state sentence forces the literal of each of its entries.
Source: mandate § Definitions (`stateOf → lit` is a conjunct)
Kind: L
Fidelity: n/a -/
theorem holds_lit_of_holds_stateOf {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) {m q : ℕ}
    {v : PCWorld} (h : v.Holds (stateOf C m q)) {c r : ℕ}
    (he : entryOf c (tableOfCode q) = some r) : v.Holds (C.literal m (sentenceOfCode c) r) :=
  (holds_stateOf C m q v).1 h (c, r) (mem_of_entryOf_eq_some he)

/-- **The pinned set of record**: the day-`(n+1)` coordinates of the index list all of whose cell
literals are small on day `n`. Every theorem quantifies over it; none assumes a full table is
small (plan risk "empty pinned set"; its non-emptiness at B2 is `InstanceB2.pinned_eventually`).
Source: mandate § Definitions (`pinned`); [[bli-program-desiderata]] §10 item 10
Kind: D
Fidelity: exact -/
def pinned {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) (index : ℕ → List ℕ) (n : ℕ) : List ℕ :=
  (index (n + 1)).filter fun c => ∀ r ∈ C.cells (n + 1), SmallOn n (C.literal (n + 1) (sentenceOfCode c) r)

/-- Membership in the pinned set.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_pinned {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) (index : ℕ → List ℕ) (n c : ℕ) :
    c ∈ pinned C index n ↔
      c ∈ index (n + 1) ∧ ∀ r ∈ C.cells (n + 1), SmallOn n (C.literal (n + 1) (sentenceOfCode c) r) := by
  simp [pinned]

/-- **The superbelief's marginal on the coordinate with code `c`, cell `r`**: the mass of the
day-`(n+1)` candidates whose table assigns `c` the grid index `r`. Indexed by the sentence
*code* (the mandate's `⌜φ⌝`), as `D_NNUcell` and `ValuesAtRep` are; `IndexCodes` says the index
lists genuine codes, so that `c = ⌜sentenceOfCode c⌝`.
Source: mandate § Definitions (`cellMass`); [[bli-program]] §3.6(i)
Kind: D
Fidelity: exact -/
noncomputable def cellMass (σ : ℕ → ℕ → Sentence) (S : StateSystem) (P : History) (n c r : ℕ) :
    ℝ :=
  ∑ q ∈ (S.states (n + 1)).filter (fun q => entryOf c (tableOfCode q) = some r), P n (σ (n + 1) q)

/-- **The index lists sentence codes**: every listed `c` is the code of the sentence it decodes
to (`witnessIndex` lists `⌜⊥⌝`, `⌜⊤⌝`). Needed wherever a code-indexed object (`cellMass`,
`ValuesAtRep`) meets a sentence-indexed one (`cellOfTable`, which matches on `⌜φ⌝`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def IndexCodes (index : ℕ → List ℕ) (m : ℕ) : Prop :=
  ∀ c ∈ index m, Encodable.encode (sentenceOfCode c) = c

/-- **D_NNUcell — exact finite-time no-net-expected-update, cell form (the definition of record
of `bli-linkage`, identical in both angles)**: on every pinned coordinate, today's price is the
representative-weighted sum of today's prices of tomorrow's cell literals.
`bli-found`'s interval `D_NNU quoteAt cells ε` is the bracket-with-width analogue
(`Fidelity: variant: cell literals and representatives in place of interval quotes and
midpoints`); `Bracket.lean` relates them.
Source: mandate § Definitions (`D_NNUcell`); [[bli-program]] §3.6(ii) (`D-NNU(Q)`)
Kind: D
Fidelity: variant: cell literals and representatives in place of interval quotes and midpoints -/
def D_NNUcell {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) (index : ℕ → List ℕ) (Q : History) :
    Prop :=
  ∀ n, ∀ c ∈ pinned C index n,
    Q n (sentenceOfCode c) =
      ∑ r ∈ C.cells (n + 1), (C.rep (n + 1) r : ℝ) * Q n (C.literal (n + 1) (sentenceOfCode c) r)

/-- **The degenerate superbelief, σ-parametric**: mass `1` on the candidate `deg n` (the table
copying today's rounded entries, at the instantiation's choice). The mandate's `S` argument is dropped: the predicate does not read the system (as `bli-found` did for `E1x`).
Source: mandate § Definitions (`Degenerate`); bli-trajectory `b0History` (B1 instance)
Kind: D
Fidelity: exact -/
def Degenerate (σ : ℕ → ℕ → Sentence) (P : History) (deg : ℕ → ℕ) : Prop :=
  ∀ n, P n (σ (n + 1) (deg n)) = 1

/-! ## The interval-side pinned set -/

/-- **The interval-pinned coordinates**: the day-`(n+1)` listed coordinates whose interval quotes,
for every interval of the finite family `ints (n+1)`, are small on day `n` (the quotes the
bracket theorems read through `E1x`).
Source: mandate § Attempt angles (B); bli-found `Constraints.D_NNU` (its smallness premise)
Kind: D
Fidelity: exact -/
def pinnedI (quote : ℕ → Sentence → ℚ → ℚ → Sentence) (ints : ℕ → Finset (ℚ × ℚ))
    (index : ℕ → List ℕ) (n : ℕ) : List ℕ :=
  (index (n + 1)).filter fun c =>
    ∀ I ∈ ints (n + 1), SmallOn n (quote (n + 1) (sentenceOfCode c) I.1 I.2)

/-- Membership in the interval-pinned set.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_pinnedI (quote : ℕ → Sentence → ℚ → ℚ → Sentence) (ints : ℕ → Finset (ℚ × ℚ))
    (index : ℕ → List ℕ) (n c : ℕ) :
    c ∈ pinnedI quote ints index n ↔
      c ∈ index (n + 1) ∧
        ∀ I ∈ ints (n + 1), SmallOn n (quote (n + 1) (sentenceOfCode c) I.1 I.2) := by
  simp [pinnedI]

/-! ## Two grid conditions for the stage-level determination theorem -/

/-- **A spurious literal entails another candidate**: on day `n+1`, if a candidate `q` does not
assign the indexed coordinate `c` the cell `r`, then some *other* candidate `q'` is entailed by
`σ q` together with the literal `lit c r`. True of every full product grid (change `q`'s entry
at `c` to `r`) and of `Grid.fixedStates` (`InstanceB2.fixedStates_spuriousEntails`). This is the
one grid property the propositional determination theorem needs in place of the completed
theory's exclusivity of literals.
Source: this package (`Determination.determination_stage`); mandate K1 (traps)
Kind: D
Fidelity: n/a -/
def SpuriousEntails (σ : ℕ → ℕ → Sentence) (literal : ℕ → Sentence → ℕ → Sentence) (S : StateSystem)
    (index : ℕ → List ℕ) (cells : ℕ → Finset ℕ) (n : ℕ) : Prop :=
  ∀ q ∈ S.states (n + 1), ∀ c ∈ index (n + 1), ∀ r ∈ cells (n + 1),
    entryOf c (tableOfCode q) ≠ some r →
      ∃ q' ∈ S.states (n + 1), q' ≠ q ∧ ∀ v : PCWorld, v.Holds (σ (n + 1) q) →
        v.Holds (literal (n + 1) (sentenceOfCode c) r) → v.Holds (σ (n + 1) q')

/-- **Every candidate values every indexed coordinate at the representative of a legitimate cell
it lists.** The B2 system's `val` (`b2StateSystem`: `rep m` of the entry) on a grid whose tables
cover the index with entries in `cells`.
Source: mandate K2 (`hval`); bli-found `StateSentence.b2StateSystem`
Kind: D
Fidelity: n/a -/
def ValuesAtRep {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) (S : StateSystem) (index : ℕ → List ℕ)
    (n : ℕ) : Prop :=
  ∀ q ∈ S.states (n + 1), ∀ c ∈ index (n + 1),
    ∃ r ∈ C.cells (n + 1), entryOf c (tableOfCode q) = some r ∧
      S.val (n + 1) q (sentenceOfCode c) = C.rep (n + 1) r

end Cleanroom.Bli.BliLinkageB
