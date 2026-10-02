import Cleanroom.Bli.BliFound
import Cleanroom.Bli.BliFinite

/-!
# `bli-trajectory` · Defs: the constructed market `𝐏` over an abstract base (F8, D1–D4)

The definitions of record of the package `bli-trajectory` (namespace
`Cleanroom.Bli.BliTrajectory`; mandate [[bli-trajectory-mandate]] §D1–D4; program
[[bli-program]] §2.5). Everything here is stated over `bli-found`'s objects (`smallSet`,
`stateAtom`, `StateSystem`, the constraint predicates) and `bli-finite`'s (`Table`, `Mesh`,
`grid`, `Kernel`, `Skeleton`, `trajLaw`, `actualTable`, `roundTo`).

Design decisions of record (each is disclosed in [[bli-trajectory-findings]]):

* **The index is `bli-found`'s small set** (`smallIndex`). Concrete evaluation over it is
  impossible (`smallSet 1` already has more than 16 elements), so every witness over
  `smallIndex` is proved from theorems.
* **The coding is a parameter with a largeness field** (`StateCoding`; deviation from
  [[bli-program]] §2.3's `encode (m, Q̂)`): `bliPrice` prices small sentences by the base
  *first*, so a day-`(n+1)` state atom small on day `n` would be priced by `Q`, not the kernel;
  `StateCoding.large` plus `stateAtom_large` keeps every future state atom out of the small case.
  A computable coding is `bli-found` stretch S1's business and `bli-assemble`'s `COMP` waits on
  it; nothing here claims it.
* **Tier A is coding-aware** (deviation from the mandate's D2, made precise): the parser
  `parse c n` recognises a state atom `stateAtom m q` as a *state* only when `n < m` and `q` is a
  candidate code of the system (`q ∈ (grid …).image (c.code m)`); every other sentence with no
  such atom is an opaque "small part". Conjunction trees are split at `⋏` only where a future
  state atom occurs beneath; `⊤` is neutral exactly as the tail of a right-nested chain
  (`stateConj`'s shape) and opaque elsewhere. Consequences: (i) a day-`n`-small sentence never
  contains a future state atom (they are large), so `bli_update_small` holds on all of
  `smallSet n`; (ii) the scope restriction of the faith lemmas is exactly Known issue 1's
  antecedent, "`φ` mentions no state atom of a day in `(n, m)`" (`NoFutureState c n φ`).
* **The chain probability is the forward recursion** `chainProbH` (first day first), not a sum
  over `bli-finite`'s snoc-oriented `trajGrid`; `Marginals.chainProbH_eq_trajMass` identifies the
  two (the forward probability is the mass `trajLaw` gives the chain's event), and
  `Parser.chainProbH_sum_states` is the additivity over a day's codes. This is what makes
  the update identities (restart from the conditioned table) definitional.
* **B0 (the degenerate solution) is built directly** (`b0History`), by the deterministic
  continuation `degAt`, because the point-mass kernel is not a `Kernel` (balance fails off the
  denominator grid). No tent fallback is smuggled in.

Sources: Appendix B (`main.tex:431–449`), bli-slides-017, [[bli-program]] §2.5–2.6, the mandate.
-/

namespace Cleanroom.Bli.BliTrajectory

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite

open Classical

noncomputable section

/-! ## D1. The index, the coding, the B1 state system -/

/-- **The index of record**: `bli-found`'s `smallSet`, nested by `smallSet_mono`.
Source: [[bli-program]] §2.1; mandate D1
Kind: D
Fidelity: exact -/
def smallIndex : SmallIndex := ⟨smallSet, fun m => smallSet_mono (Nat.le_succ m)⟩

/-- Unfolding lemma for `smallIndex`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma smallIndex_S (m : ℕ) : smallIndex.S m = smallSet m := rfl

/-- **A state coding** for a mesh: a code for every day-`m` table, injective on the day-`m` grid,
whose codes on the grid are *large* (`sizeBound m ≤ Nat.log 4 (code m Q)`, so by
`stateAtom_large` every candidate's state atom is large on every day up to its own). Deviation
from [[bli-program]] §2.3 (`encode (m, Q̂)`): the coding is a parameter, and largeness is a field
because `bliPrice`'s small-first case order needs it. A *computable* coding is `bli-found`
stretch S1's business and `bli-assemble`'s `COMP` waits on it — not claimed here.
Source: [[bli-program]] §2.3; mandate D1 (deviation, disclosed)
Kind: D
Fidelity: variant: parameter with a largeness field (disclosed) -/
structure StateCoding (𝓜 : Mesh) where
  /-- The write-out code of a day-`m` table. -/
  code : ∀ m, Table smallIndex m → ℕ
  /-- Injective on the day-`m` grid. -/
  inj : ∀ m, Set.InjOn (code m) ↑(grid smallIndex 𝓜.d m)
  /-- Codes of grid tables are large. -/
  large : ∀ m, ∀ Q ∈ grid smallIndex 𝓜.d m, sizeBound m ≤ Nat.log 4 (code m Q)

namespace StateCoding

variable {𝓜 : Mesh} (c : StateCoding 𝓜)

/-- The candidate codes of day `m`: the image of the grid.
Source: mandate D1
Kind: D
Fidelity: exact -/
def states (m : ℕ) : Finset ℕ := (grid smallIndex 𝓜.d m).image (c.code m)

/-- **Decoding**: the grid table with code `q` if there is one (unique by `inj`), else the
**junk zero table** (a fixed table off the image; `tableVal` reads it as `0` everywhere).
Source: mandate D1
Kind: D
Fidelity: n/a (junk value disclosed) -/
def decode (m q : ℕ) : Table smallIndex m :=
  if h : ∃ Q ∈ grid smallIndex 𝓜.d m, c.code m Q = q then h.choose else fun _ => 0

/-- Decoding a grid table's code gives the table back.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma decode_code {m : ℕ} {Q : Table smallIndex m} (hQ : Q ∈ grid smallIndex 𝓜.d m) :
    c.decode m (c.code m Q) = Q := by
  unfold decode
  have h : ∃ Q' ∈ grid smallIndex 𝓜.d m, c.code m Q' = c.code m Q := ⟨Q, hQ, rfl⟩
  rw [dif_pos h]
  exact c.inj m h.choose_spec.1 hQ h.choose_spec.2

/-- A candidate code decodes to a grid table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma decode_mem_grid {m q : ℕ} (hq : q ∈ c.states m) :
    c.decode m q ∈ grid smallIndex 𝓜.d m := by
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hq
  rw [c.decode_code hQ]; exact hQ

/-- Off the candidate codes, decoding is the zero table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma decode_of_not_mem {m q : ℕ} (hq : q ∉ c.states m) : c.decode m q = fun _ => 0 := by
  unfold decode
  rw [dif_neg]
  rintro ⟨Q, hQ, rfl⟩
  exact hq (Finset.mem_image_of_mem _ hQ)

/-- The code of a grid table is a candidate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma code_mem_states {m : ℕ} {Q : Table smallIndex m} (hQ : Q ∈ grid smallIndex 𝓜.d m) :
    c.code m Q ∈ c.states m := Finset.mem_image_of_mem _ hQ

/-- Every candidate code is large: `sizeBound m ≤ Nat.log 4 q`.
Source: mandate D1 (`large`)
Kind: L
Fidelity: n/a -/
lemma large_of_mem {m q : ℕ} (hq : q ∈ c.states m) : sizeBound m ≤ Nat.log 4 q := by
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hq
  exact c.large m Q hQ

/-- **A candidate's state atom is large on every day up to its own** (`stateAtom_large`).
Source: mandate D1; `bli-found` `stateAtom_large`
Kind: L
Fidelity: exact -/
lemma stateAtom_large_of_mem {m q : ℕ} (hq : q ∈ c.states m) :
    ∀ n ≤ m, ¬ SmallOn n (stateAtom m q) :=
  stateAtom_large (c.large_of_mem hq)

/-- The rational table value of code `q` at a sentence: the decoded table's entry if `φ` is small
on day `m`, else the junk `0` (reached by no predicate: `Sminus m m ⊆ smallSet m`, and `E4` reads
day-`(n+1)` tables on `smallSet n ⊆ smallSet (n+1)`).
Source: mandate D1
Kind: D
Fidelity: n/a (junk value disclosed) -/
def tableVal (m q : ℕ) (φ : Sentence) : ℚ :=
  if h : φ ∈ smallSet m then c.decode m q ⟨φ, h⟩ else 0

/-- Unfolding `tableVal` at a small sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tableVal_of_mem {m q : ℕ} {φ : Sentence} (h : φ ∈ smallSet m) :
    c.tableVal m q φ = c.decode m q ⟨φ, h⟩ := by
  unfold tableVal; rw [dif_pos h]

/-- The table value of a grid table's code is the table's entry.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tableVal_code {m : ℕ} {Q : Table smallIndex m} (hQ : Q ∈ grid smallIndex 𝓜.d m)
    {φ : Sentence} (h : φ ∈ smallSet m) :
    c.tableVal m (c.code m Q) φ = Q ⟨φ, h⟩ := by
  rw [c.tableVal_of_mem h, c.decode_code hQ]

/-- Table values lie in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tableVal_mem_Icc (m q : ℕ) (φ : Sentence) : 0 ≤ c.tableVal m q φ ∧ c.tableVal m q φ ≤ 1 := by
  unfold tableVal
  split_ifs with h
  · by_cases hq : q ∈ c.states m
    · exact inUnit_of_mem_grid (c.decode_mem_grid hq) _
    · rw [c.decode_of_not_mem hq]; exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨le_rfl, zero_le_one⟩

end StateCoding

/-- **A state coding exists** (noncomputably): index the grid by `Finset.equivFin` and offset by
`4 ^ sizeBound m` (the model is `PaperInstances.largeStates`).
Source: mandate D1 (`exists_stateCoding`)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem exists_stateCoding (𝓜 : Mesh) : Nonempty (StateCoding 𝓜) := by
  refine ⟨{ code := fun m Q => if h : Q ∈ grid smallIndex 𝓜.d m
              then 4 ^ sizeBound m + ((grid smallIndex 𝓜.d m).equivFin ⟨Q, h⟩ : ℕ) else 0
            inj := ?_, large := ?_ }⟩
  · intro m Q hQ Q' hQ' h
    simp only [Finset.mem_coe] at hQ hQ'
    simp only [dif_pos hQ, dif_pos hQ', add_right_inj, Fin.val_inj] at h
    have := (grid smallIndex 𝓜.d m).equivFin.injective h
    exact congrArg Subtype.val this
  · intro m Q hQ
    simp only [dif_pos hQ]
    calc sizeBound m = Nat.log 4 (4 ^ sizeBound m) := (Nat.log_pow (by norm_num) _).symm
      _ ≤ _ := Nat.log_mono_right (Nat.le_add_right _ _)

/-- **The B1 state system** over a base `Q`, a mesh and a coding: candidates are the codes of
the grid, `val` reads the decoded table (junk `0` off `smallSet m`), and the realized state is
the code of the rounded actual table.
Source: [[bli-program]] §2.3/§2.5; mandate D1
Kind: D
Fidelity: exact (junk values disclosed in `StateCoding.decode`/`tableVal`) -/
def bliStateSystem (Q : RatHistory) (𝓜 : Mesh) (c : StateCoding 𝓜) : StateSystem where
  states := c.states
  val m q φ := (c.tableVal m q φ : ℝ)
  actual m := c.code m (actualState smallIndex 𝓜.d Q m)
  actual_mem _ := c.code_mem_states actualState_mem_grid

/-- Unfolding lemmas for `bliStateSystem`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma bliStateSystem_states (Q : RatHistory) (𝓜 : Mesh) (c : StateCoding 𝓜) (m : ℕ) :
    (bliStateSystem Q 𝓜 c).states m = c.states m := rfl

/-- `bliStateSystem_val`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma bliStateSystem_val (Q : RatHistory) (𝓜 : Mesh) (c : StateCoding 𝓜) (m q : ℕ)
    (φ : Sentence) : (bliStateSystem Q 𝓜 c).val m q φ = (c.tableVal m q φ : ℝ) := rfl

/-- `bliStateSystem_actual`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma bliStateSystem_actual (Q : RatHistory) (𝓜 : Mesh) (c : StateCoding 𝓜) (m : ℕ) :
    (bliStateSystem Q 𝓜 c).actual m = c.code m (actualState smallIndex 𝓜.d Q m) := rfl

/-! ## D2. Tier A: the parser -/

/-- Read `(day, code)` off an atom index carrying the state tag.
Source: mandate D2
Kind: D
Fidelity: n/a -/
def stateData (a : ℕ) : Option (ℕ × ℕ) :=
  if a.unpair.1 = stateTag then some a.unpair.2.unpair else none

/-- A state atom's index reads back its data.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma stateData_freshAtomCode (m q : ℕ) :
    stateData (freshAtomCode stateFamily (Nat.pair m q)) = some (m, q) := by
  simp [stateData, freshAtomCode, stateTag, Nat.unpair_pair]

/-- An atom whose index reads as `(m, q)` is `stateAtom m q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atom_eq_stateAtom_of_stateData {a m q : ℕ} (h : stateData a = some (m, q)) :
    Formula.atom a = stateAtom m q := by
  unfold stateData at h
  split_ifs at h with htag
  · simp only [Option.some.injEq] at h
    have h1 : a.unpair.2 = Nat.pair m q := by
      rw [← Nat.pair_unpair a.unpair.2, h]
    have h2 : a = Nat.pair stateTag (Nat.pair m q) := by
      rw [← h1, ← htag, Nat.pair_unpair]
    rw [h2]; rfl

/-- `hasFutureAtom c n ψ`: some state atom of a day `> n` with a candidate code occurs in `ψ`.
Source: mandate D2 (made precise: coding-aware)
Kind: D
Fidelity: n/a -/
def hasFutureAtom {𝓜 : Mesh} (c : StateCoding 𝓜) (n : ℕ) : Sentence → Bool
  | .atom a => match stateData a with
      | some (m, q) => decide (n < m ∧ q ∈ c.states m)
      | none => false
  | .falsum => false
  | .and φ ψ => hasFutureAtom c n φ || hasFutureAtom c n ψ
  | .or φ ψ => hasFutureAtom c n φ || hasFutureAtom c n ψ
  | .imp φ ψ => hasFutureAtom c n φ || hasFutureAtom c n ψ

/-- **`NoFutureState c n φ`**: `φ` mentions no state atom (candidate code) of a day `> n`. This
is the scope restriction of every "scoped" faith predicate below — Known issue 1's antecedent
made into a predicate.
Source: mandate M1/M9 (Known issue 1)
Kind: D
Fidelity: n/a -/
def NoFutureState {𝓜 : Mesh} (c : StateCoding 𝓜) (n : ℕ) (φ : Sentence) : Prop :=
  hasFutureAtom c n φ = false

/-- The future-state-atom test: `some (m, q)` iff `ψ = stateAtom m q` with `n < m` and `q` a
candidate.
Source: mandate D2
Kind: D
Fidelity: n/a -/
def futureStateAtom {𝓜 : Mesh} (c : StateCoding 𝓜) (n : ℕ) : Sentence → Option (ℕ × ℕ)
  | .atom a => match stateData a with
      | some (m, q) => if n < m ∧ q ∈ c.states m then some (m, q) else none
      | none => none
  | _ => none

/-- Combine two parses: append the chains, keep the (at most one) small part.
Source: mandate D2
Kind: D
Fidelity: n/a -/
def combine : Option (List (ℕ × ℕ) × Option Sentence) →
    Option (List (ℕ × ℕ) × Option Sentence) → Option (List (ℕ × ℕ) × Option Sentence)
  | some (l₁, none), some (l₂, s) => some (l₁ ++ l₂, s)
  | some (l₁, some φ), some (l₂, none) => some (l₁ ++ l₂, some φ)
  | some (_, some _), some (_, some _) => none
  | none, _ => none
  | some _, none => none

/-- **The Tier-A parser.** A sentence with no future state atom is an opaque small part. A
future state atom is a one-element chain. A conjunction (beneath which a future state atom
occurs) combines the parses of its conjuncts, except that `⊤` right after a future state atom
is the neutral chain tail (so `stateConj l` parses). A disjunction or implication containing a
future state atom is Tier B (`none`).
Source: mandate D2 (made precise); [[bli-program]] §2.5
Kind: D
Fidelity: variant: coding-aware, conjunction trees split at `⋏`, `⊤` neutral only as chain tail -/
def parse {𝓜 : Mesh} (c : StateCoding 𝓜) (n : ℕ) : Sentence → Option (List (ℕ × ℕ) × Option Sentence)
  | .atom a => match futureStateAtom c n (.atom a) with
      | some x => some ([x], none)
      | none => some ([], some (.atom a))
  | .falsum => some ([], some .falsum)
  | .and φ χ =>
      if hasFutureAtom c n (.and φ χ) then
        combine (parse c n φ)
          (if χ = ⊤ ∧ (futureStateAtom c n φ).isSome then some ([], none) else parse c n χ)
      else some ([], some (.and φ χ))
  | .or φ χ => if hasFutureAtom c n (.or φ χ) then none else some ([], some (.or φ χ))
  | .imp φ χ => if hasFutureAtom c n (.imp φ χ) then none else some ([], some (.imp φ χ))

/-- The entry of a chain with the latest day (leftmost among ties; `(0, 0)` for the empty list).
Source: mandate D2
Kind: D
Fidelity: n/a -/
def latestEntry (l : List (ℕ × ℕ)) : ℕ × ℕ :=
  l.foldr (fun x acc => if acc.1 ≤ x.1 then x else acc) (0, 0)

/-- **Consistency** of a chain: entries sharing a day share the code (what `E5`'s exclusivity
reads: an inconsistent chain prices `0`).
Source: mandate D2
Kind: D
Fidelity: n/a -/
def Consistent (l : List (ℕ × ℕ)) : Prop := ∀ x ∈ l, ∀ y ∈ l, x.1 = y.1 → x.2 = y.2

/-- The small part (if any) is small on day `m`.
Source: mandate D2
Kind: D
Fidelity: n/a -/
def SmallPart (m : ℕ) : Option Sentence → Prop
  | none => True
  | some φ => SmallOn m φ

/-- **`tierA c n ψ`**: the parse of `ψ` if it has a nonempty chain and its small part is small on
the latest day; else `none` (Tier B).
Source: mandate D2; [[bli-program]] §2.5
Kind: D
Fidelity: variant (see `parse`) -/
def tierA {𝓜 : Mesh} (c : StateCoding 𝓜) (n : ℕ) (ψ : Sentence) :
    Option (List (ℕ × ℕ) × Option Sentence) :=
  match parse c n ψ with
  | some (l, s) => if l ≠ [] ∧ SmallPart (latestEntry l).1 s then some (l, s) else none
  | none => none


/-! ## D2 (continued). The chain probability, the prices, the history -/

variable {𝓜 : Mesh}

/-- **The forward chain probability.** Starting from the day-`n` table `t`, the probability under
the skeleton that the next `H` days' tables carry the codes listed in `l` on their days (entries
of `l` whose day is `≤ n` or `> n + H` are inert). Defined by the *first-day-first* recursion
`chainProbH l n t (H+1) = ∑_Q κ_n(t)(Q) · [l's day-(n+1) entries code Q] · chainProbH l (n+1) Q H`
— the chain rule is built in, which is what makes the restart-from-the-conditioned-table
identities (`Update.lean`) definitional. `Marginals.chainProbH_eq_trajMass` identifies it with
the mass `bli-finite`'s `trajLaw` gives the same event.
Source: [[bli-program]] §2.5 (`tierAPrice` as a marginal of `trajLaw`); bli-soto-a-035 (chain rule); mandate D2
Kind: D
Fidelity: variant: forward recursion in place of a `trajGrid` sum (identified by theorem) -/
def chainProbH (sk : Skeleton smallIndex 𝓜.d) (c : StateCoding 𝓜) (l : List (ℕ × ℕ)) :
    (n : ℕ) → Table smallIndex n → ℕ → ℚ
  | _, _, 0 => 1
  | n, t, H + 1 => ∑ Q ∈ grid smallIndex 𝓜.d (n + 1),
      (sk.κ n).law t Q *
        (if ∀ x ∈ l, x.1 = n + 1 → c.code (n + 1) Q = x.2 then chainProbH sk c l (n + 1) Q H
         else 0)

/-- The mass of a chain: the forward probability run to the chain's latest day.
Source: mandate D2
Kind: D
Fidelity: exact -/
def chainMass (sk : Skeleton smallIndex 𝓜.d) (c : StateCoding 𝓜) (n : ℕ) (t : Table smallIndex n)
    (l : List (ℕ × ℕ)) : ℚ :=
  chainProbH sk c l n t ((latestEntry l).1 - n)

/-- The value of the small part: `1` if absent, else the latest day's table at it.
Source: mandate D2
Kind: D
Fidelity: exact -/
def smallFactor (c : StateCoding 𝓜) (l : List (ℕ × ℕ)) : Option Sentence → ℚ
  | none => 1
  | some φ => c.tableVal (latestEntry l).1 (latestEntry l).2 φ

/-- **The Tier-A price** of a parsed sentence: `0` if the chain is inconsistent (two codes on
one day), else the chain mass times the small factor read off the **latest** day's table (as
`E3`/`E3fin` demand).
Source: mandate D2; Appendix B constraints 2–3 (`main.tex:432–433`)
Kind: D
Fidelity: exact -/
def tierAPrice (sk : Skeleton smallIndex 𝓜.d) (c : StateCoding 𝓜) (n : ℕ) (t : Table smallIndex n) :
    List (ℕ × ℕ) × Option Sentence → ℚ
  | (l, s) => if Consistent l then chainMass sk c n t l * smallFactor c l s else 0

/-- **`bliPrice`**: small sentences by the base (constraint 1, exact), Tier-A sentences by the
trajectory prior started from the **unrounded** actual table, everything else (Tier B) by the
base. Case order is load-bearing: small-first makes a past state atom that has become small the
base's, and `StateCoding.large` keeps every future atom out of the small case.
Source: [[bli-program]] §2.5; mandate D2
Kind: D
Fidelity: exact -/
def bliPrice (Q : RatHistory) (𝓜 : Mesh) (sk : Skeleton smallIndex 𝓜.d) (c : StateCoding 𝓜)
    (n : ℕ) (ψ : Sentence) : ℚ :=
  if SmallOn n ψ then Q n ψ else
    match tierA c n ψ with
    | some s => tierAPrice sk c n (actualTable smallIndex Q n) s
    | none => Q n ψ

/-- **`bliHistory`**: `bliPrice` as an FAF `History` (real-valued).
Source: [[bli-program]] §2.5; mandate D2
Kind: D
Fidelity: exact -/
def bliHistory (Q : RatHistory) (𝓜 : Mesh) (sk : Skeleton smallIndex 𝓜.d) (c : StateCoding 𝓜) :
    History :=
  fun n ψ => (bliPrice Q 𝓜 sk c n ψ : ℝ)

/-- A rational history as an FAF `History` (for `E1x`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def ratHistory (Q : RatHistory) : History := fun n φ => (Q n φ : ℝ)

/-! ## D3. B0, the degenerate solution -/

/-- Point mass at a table.
Source: Appendix B (`main.tex:447`); mandate D3
Kind: D
Fidelity: exact -/
def pointMass {𝒮 : SmallIndex} {m : ℕ} (t : Table 𝒮 m) : Superbelief 𝒮 m :=
  fun Q => if Q = t then 1 else 0

/-- Extend a day-`m` table to day `m+1` by `0` on the new coordinates (a disclosed convention:
the sources say nothing about new sentences; `0 ∈ gridVals`).
Source: mandate D3 (convention, disclosed)
Kind: D
Fidelity: n/a -/
def extendZero {𝒮 : SmallIndex} {m : ℕ} (t : Table 𝒮 m) : Table 𝒮 (m + 1) :=
  fun φ => if h : φ.1 ∈ 𝒮.S m then t ⟨φ.1, h⟩ else 0

/-- The degenerate step: round the day-`m` table to the day-`(m+1)` grid values and extend by
zero.
Source: Appendix B (`main.tex:447`); mandate D3
Kind: D
Fidelity: exact (rounded to the *next* day's grid; new coordinates `0`) -/
def degStep {𝒮 : SmallIndex} (d : ℕ → ℕ) (m : ℕ) (t : Table 𝒮 m) : Table 𝒮 (m + 1) :=
  extendZero (roundTo (d (m + 1)) t)

/-- The degenerate law: mass `1` on the degenerate step. **Not a `Kernel`**: balance fails at
every unit-cube table off the denominator grid (`Degenerate.lean`).
Source: Appendix B (`main.tex:447`); mandate D3
Kind: D
Fidelity: exact -/
def degLaw {𝒮 : SmallIndex} (d : ℕ → ℕ) (m : ℕ) (t : Table 𝒮 m) : Superbelief 𝒮 (m + 1) :=
  pointMass (degStep d m t)

/-- The iterated degenerate continuation of a day-`n` table.
Source: mandate D3
Kind: D
Fidelity: n/a -/
def degIter {𝒮 : SmallIndex} (d : ℕ → ℕ) {n : ℕ} (t : Table 𝒮 n) : (h : ℕ) → Table 𝒮 (n + h)
  | 0 => t
  | h + 1 => degStep d (n + h) (degIter d t h)

/-- The degenerate continuation on an explicit day `j ≥ n` (the junk zero table for `j < n`).
Source: mandate D3
Kind: D
Fidelity: n/a -/
def degAt {𝒮 : SmallIndex} (d : ℕ → ℕ) {n : ℕ} (t : Table 𝒮 n) (j : ℕ) : Table 𝒮 j :=
  if h : n ≤ j then (degIter d t (j - n)).castDay (by omega) else fun _ => 0

/-- **B0's price**: as `bliPrice`, with the trajectory prior replaced by the deterministic
continuation — a Tier-A chain prices `1` (times the small factor) iff every entry is the code of
the continuation on its day, else `0`.
Source: Appendix B (`main.tex:447`, the degenerate solution); mandate D3
Kind: D
Fidelity: exact -/
def b0Price (Q : RatHistory) (𝓜 : Mesh) (c : StateCoding 𝓜) (n : ℕ) (ψ : Sentence) : ℚ :=
  if SmallOn n ψ then Q n ψ else
    match tierA c n ψ with
    | some (l, s) =>
        if ∀ x ∈ l, x.2 = c.code x.1 (degAt 𝓜.d (actualTable smallIndex Q n) x.1)
        then smallFactor c l s else 0
    | none => Q n ψ

/-- **B0's history** (the degenerate solution) as an FAF `History`.
Source: Appendix B (`main.tex:447`); mandate D3
Kind: D
Fidelity: exact -/
def b0History (Q : RatHistory) (𝓜 : Mesh) (c : StateCoding 𝓜) : History :=
  fun n ψ => (b0Price Q 𝓜 c n ψ : ℝ)

/-! ## D4. Helpers over the abstract system -/

/-- The mass of the event "`𝑸_m(φ) = x`" **as a sum over the partition** (not a disjunction
sentence — B1 prices no disjunction of state atoms; deviation disclosed `(c)`).
Source: bli-slides-015 (i); mandate D4
Kind: D
Fidelity: variant: (c) event as a partition sum -/
def marginalMass (S : StateSystem) (P : History) (n m : ℕ) (φ : Sentence) (x : ℝ) : ℝ :=
  ∑ q ∈ (S.states m).filter (fun q => S.val m q φ = x), P n (stateAtom m q)

/-- The joint mass of `φ` with the event "`𝑸_m(φ) = x`", as a partition sum.
Source: bli-slides-015 (i); mandate D4
Kind: D
Fidelity: variant: (c) event as a partition sum -/
def marginalJoint (S : StateSystem) (P : History) (n m : ℕ) (φ : Sentence) (x : ℝ) : ℝ :=
  ∑ q ∈ (S.states m).filter (fun q => S.val m q φ = x), P n (φ ⋏ stateAtom m q)

/-- **`FaithMarginal`** (bli-slides-015 (ii); the Notion's "conditional trust in future beliefs"
`P_n(φ | P_m(φ) = p) = p`), product form over the partition sums.
Source: bli-slides-015 (ii); [[bli-soto-a-inventory]] 008/009; mandate D4
Kind: D
Fidelity: variant: product form, partition sums -/
def FaithMarginal (S : StateSystem) (P : History) : Prop :=
  ∀ n m, n < m → ∀ φ ∈ Sminus m m, ∀ x : ℝ,
    marginalJoint S P n m φ x = x * marginalMass S P n m φ x

/-- **`BayesRatio`**: the ratio form of the update at `(n, ψ)`, under positivity of the realized
next state, with Lean's `/` on `ℝ` — never `conditionalQuote`.
Source: Appendix B (`main.tex:440`); mandate D4
Kind: D
Fidelity: exact (ratio form under explicit positivity) -/
def BayesRatio (S : StateSystem) (P : History) (n : ℕ) (ψ : Sentence) : Prop :=
  0 < P n (stateAtom (n + 1) (S.actual (n + 1))) →
    P (n + 1) ψ = P n (ψ ⋏ stateAtom (n + 1) (S.actual (n + 1))) /
      P n (stateAtom (n + 1) (S.actual (n + 1)))

/-- **`TB_on A`**: `bli-found`'s `TB` restricted to the sentences `A n ψ`.
Source: bli-slides-048; mandate D4
Kind: D
Fidelity: exact (restriction) -/
def TB_on (A : ℕ → Sentence → Prop) (S : StateSystem) (P : History) : Prop :=
  ∀ n ψ, A n ψ →
    P (n + 1) ψ * P n (stateAtom (n + 1) (S.actual (n + 1))) =
      P n (ψ ⋏ stateAtom (n + 1) (S.actual (n + 1)))

/-- **`E2xScoped c`**: `bli-found`'s `E2x` with the scope restricted by `NoFutureState c n φ`
("`φ` mentions no state atom of a day `> n`"; Known issue 1). Weaker than `E2x` exactly there.
Source: bli-paper-035; mandate M1 (`bli_cond2_scoped`)
Kind: D
Fidelity: weaker: scope minus sentences mentioning a state atom of a day in `(n, m)` -/
def E2xScoped (c : StateCoding 𝓜) (S : StateSystem) (P : History) : Prop :=
  ∀ n m, n < m → ∀ q ∈ S.states m, ∀ φ ∈ Sminus m m, NoFutureState c n φ →
    P n (φ ⋏ stateAtom m q) = S.val m q φ * P n (stateAtom m q)

/-- **`E3Scoped c`**: `bli-found`'s `E3` with the same scope restriction.
Source: bli-paper-036; mandate M1 (`bli_cond3_scoped`)
Kind: D
Fidelity: weaker: scope restricted as `E2xScoped` -/
def E3Scoped (c : StateCoding 𝓜) (S : StateSystem) (P : History) : Prop :=
  ∀ n m o, n < m → m < o → ∀ q₁ ∈ S.states m, ∀ q₂ ∈ S.states o, ∀ φ ∈ Sminus m m,
    NoFutureState c n φ →
    P n (φ ⋏ (stateAtom m q₁ ⋏ stateAtom o q₂)) =
      S.val o q₂ φ * P n (stateAtom m q₁ ⋏ stateAtom o q₂)

/-- **`E3finScoped c`**: `bli-found`'s `E3fin` with the same scope restriction.
Source: bli-paper-036; mandate M1 (`bli_cond3_scoped`)
Kind: D
Fidelity: weaker: scope restricted as `E2xScoped` -/
def E3finScoped (c : StateCoding 𝓜) (S : StateSystem) (P : History) : Prop :=
  ∀ n (l : List (ℕ × ℕ)) (hne : l ≠ []),
    (∀ x ∈ l, n < x.1 ∧ x.2 ∈ S.states x.1) → l.IsChain (fun x y => x.1 < y.1) →
    ∀ φ ∈ Sminus (l.head hne).1 (l.head hne).1, NoFutureState c n φ →
      P n (φ ⋏ stateConj l) = S.val (l.getLast hne).1 (l.getLast hne).2 φ * P n (stateConj l)

/-- **`FaithMarginalScoped c`**: `FaithMarginal` with the same scope restriction.
Source: bli-slides-015 (ii); mandate M7 (iv)
Kind: D
Fidelity: weaker: scope restricted as `E2xScoped` -/
def FaithMarginalScoped (c : StateCoding 𝓜) (S : StateSystem) (P : History) : Prop :=
  ∀ n m, n < m → ∀ φ ∈ Sminus m m, NoFutureState c n φ → ∀ x : ℝ,
    marginalJoint S P n m φ x = x * marginalMass S P n m φ x

/-- **The scoped Roman bundle**: `E1x ∧ E2xScoped ∧ E3Scoped ∧ E4 ∧ E5` — `IsBLI_Roman` with the
two faith predicates restricted (Known issue 1).
Source: bli-slides-017; mandate M1 (`bli_isBLI_Roman_scoped`)
Kind: D
Fidelity: weaker: faith scope restricted -/
def IsBLI_RomanScoped (c : StateCoding 𝓜) (S : StateSystem) (Q P : History) : Prop :=
  E1x Q P ∧ E2xScoped c S P ∧ E3Scoped c S P ∧ E4 S P ∧ E5 S P

/-- **`KernelLip sk L`**: an ℓ¹-modulus for the skeleton — two unit-cube tables within `ε` in
every coordinate give laws within `L m · ε` in ℓ¹ (the tent's constant is `bli-superbelief`'s
business; here it is an explicit hypothesis on an abstract skeleton).
Source: mandate M6 (modulus form)
Kind: D
Fidelity: exact -/
def KernelLip {𝒮 : SmallIndex} {d : ℕ → ℕ} (sk : Skeleton 𝒮 d) (L : ℕ → ℚ) : Prop :=
  ∀ m (t t' : Table 𝒮 m) (ε : ℚ), t.InUnit → t'.InUnit → (∀ φ, |t φ - t' φ| ≤ ε) →
    ∑ Q ∈ grid 𝒮 d (m + 1), |(sk.κ m).law t Q - (sk.κ m).law t' Q| ≤ L m * ε

end

end Cleanroom.Bli.BliTrajectory
