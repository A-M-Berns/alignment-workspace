import Cleanroom.Bli.BliLinkageB.Determination
import LogicalInduction.Framework.Machine.SentenceMachine

/-!
# bli-linkage, angle B — the dissolution witness: interval linkage alone forces nothing exact

`Determination.lean` shows the trilemma survives interval linkage *for the B2 state sentence*,
because that sentence is the conjunction of its cell literals. This module shows the other
half of the mandate's decisive question: when the state sentence is linked to the quotes **only
through the open-cell interval quotes** — an *interval state sentence*
`intervalState quote cellLo cellHi m q := ⋀_{(c,r) ∈ table q} quote m φ_c (cellLo r) (cellHi r)`,
"my price for each listed coordinate lies in its open cell" — and the cell literals are atoms the
state does not entail, the whole package

`LNKcell ∧ PCPσTheory (hence PCPσ and PCPσLinked) ∧ E5σ ∧ E1x ∧ E2xσ`

is satisfiable over a base that **violates `D_NNUcell`** on a pinned coordinate. The exact-D-NNU
trilemma therefore dissolves under interval-only linkage; what survives is the bracket LP of
`Bracket.lean`.

**The witness.** One coordinate `φ₀ := atom 0` (listed as its code), two cells `0, 1` with open
neighbourhoods `(-1, 1/2)`, `(1/4, 2)` and representatives `1/4`, `3/4` (the `halfRound` shape of
`bli-found`), two candidate tables `[(⌜φ₀⌝, 0)]`, `[(⌜φ₀⌝, 1)]`. Four worlds `wld x b`: the price
`x ∈ {1/8, 7/8}` decides every interval quote ("`lo < x < hi`"), the flag `b` decides `φ₀`, every
cell literal of index `1` holds and no other does, every other atom is false. Weights
`1/8, 3/8, 3/8, 1/8`, the same mixture on every day (`dP`). Faith holds for *every* `φ` because
the state system's `val` is the conditional probability given the state (`dVal`), which at `φ₀`
is the representative. The process `dDP` reveals, by day `k`, the default-cell quotes of the
sentences small on day `k` (so `LNKcell` holds at unlisted coordinates); it decides no price, so
`theory_coherent_e1x_decides` has no `IntervalFamily` to bite with — the quote atoms are not
reflected to a fixed price, which is exactly what "interval linkage alone" means.

On every day `n` at which the two cell literals of `φ₀` are small (all `n ≥ N`,
`pinned_eventually`): `dP n φ₀ = 1/2` while `∑_r rep_r · dP n (lit_r) = 3/4`.

Grade: **N+** — two candidates with distinct tables, each of mass `1/2`, two cells, the base
uncertain about the coordinate and about tomorrow's cell.
-/

namespace Cleanroom.Bli.BliLinkageB

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

/-- **The interval state sentence**: the conjunction, over the table's entries `(c, r)`, of the
open-cell quote `quote m (sentenceOfCode c) (cellLo m r) (cellHi m r)` — "my price for `c` lies
in the open neighbourhood of cell `r`". Linked to the interval quotes propositionally, and to
nothing else.
Source: mandate § Attempt angles (B: "the weaker linkage under which the trilemma dissolves")
Kind: D
Fidelity: variant: a state family of this package's own, not the B2 `stateSentence` -/
def intervalState (quote : ℕ → Sentence → ℚ → ℚ → Sentence) (cellLo cellHi : ℕ → ℕ → ℚ)
    (m q : ℕ) : Sentence :=
  conjList ((tableOfCode q).map fun e =>
    quote m (sentenceOfCode e.1) (cellLo m e.2) (cellHi m e.2))

namespace Dissolve

/-! ## Atoms -/

/-- The coordinate: the tag-`0` atom `0` (in `Sminus m m` for every `m ≥ 1`, as `bli-trajectory`'s
`cohAtom`).
Source: none: witness
Kind: D
Fidelity: n/a -/
def dPhi : Sentence := Formula.atom 0

/-- The coordinate's code.
Source: none: witness
Kind: D
Fidelity: n/a -/
def dC0 : ℕ := Encodable.encode dPhi

/-- `sentenceOfCode dC0 = dPhi`.
Source: none: witness
Kind: L
Fidelity: n/a -/
@[simp] lemma sentenceOfCode_dC0 : sentenceOfCode dC0 = dPhi := sentenceOfCode_encode dPhi

/-- The index: the one coordinate, every day.
Source: none: witness
Kind: D
Fidelity: n/a -/
def dIndex (_m : ℕ) : List ℕ := [dC0]

/-- Family numbers for the witness's quote and literal atoms (unregistered; they only need to
be distinct from each other and from `0`).
Source: none: witness
Kind: D
Fidelity: n/a -/
def quoteFam : ℕ := 100

/-- See `quoteFam`.
Source: none: witness
Kind: D
Fidelity: n/a -/
def litFam : ℕ := 101

/-- The quote atom's index `⟨9 + quoteFam, ⟨m, ⟨c, ⌜(lo, hi)⌝⟩⟩⟩`.
Source: none: witness
Kind: D
Fidelity: n/a -/
def qIdx (m c : ℕ) (lo hi : ℚ) : ℕ :=
  freshAtomCode quoteFam (Nat.pair m (Nat.pair c (Encodable.encode (lo, hi))))

/-- The literal atom's index `⟨9 + litFam, ⟨m, ⟨c, r⟩⟩⟩`.
Source: none: witness
Kind: D
Fidelity: n/a -/
def lIdx (m c r : ℕ) : ℕ := freshAtomCode litFam (Nat.pair m (Nat.pair c r))

/-- The witness's interval quote "`lo < 𝑸_m(φ) < hi`": an atom.
Source: none: witness
Kind: D
Fidelity: n/a -/
def dQuote (m : ℕ) (φ : Sentence) (lo hi : ℚ) : Sentence :=
  Formula.atom (qIdx m (Encodable.encode φ) lo hi)

/-- The witness's cell literal "`round_m(𝑸_m(φ)) = r`": an atom the state sentence does not
entail.
Source: none: witness
Kind: D
Fidelity: n/a -/
def dLit (m : ℕ) (φ : Sentence) (r : ℕ) : Sentence := Formula.atom (lIdx m (Encodable.encode φ) r)

/-- `qIdx` is injective.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma qIdx_inj {m c m' c' : ℕ} {lo hi lo' hi' : ℚ} :
    qIdx m c lo hi = qIdx m' c' lo' hi' ↔ m = m' ∧ c = c' ∧ lo = lo' ∧ hi = hi' := by
  unfold qIdx freshAtomCode
  rw [Nat.pair_eq_pair, Nat.pair_eq_pair, Nat.pair_eq_pair, Encodable.encode_inj, Prod.mk.injEq]
  tauto

/-- `lIdx` is injective.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma lIdx_inj {m c r m' c' r' : ℕ} :
    lIdx m c r = lIdx m' c' r' ↔ m = m' ∧ c = c' ∧ r = r' := by
  unfold lIdx freshAtomCode
  rw [Nat.pair_eq_pair, Nat.pair_eq_pair, Nat.pair_eq_pair]
  tauto

/-- A quote index is never `0`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma qIdx_ne_zero (m c : ℕ) (lo hi : ℚ) : qIdx m c lo hi ≠ 0 := by
  intro h
  have h1 := Nat.left_le_pair (cleanroomBaseTag + quoteFam)
    (Nat.pair m (Nat.pair c (Encodable.encode (lo, hi))))
  unfold qIdx freshAtomCode at h
  rw [h] at h1
  unfold cleanroomBaseTag quoteFam at h1
  omega

/-- A literal index is never `0`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma lIdx_ne_zero (m c r : ℕ) : lIdx m c r ≠ 0 := by
  intro h
  have h1 := Nat.left_le_pair (cleanroomBaseTag + litFam) (Nat.pair m (Nat.pair c r))
  unfold lIdx freshAtomCode at h
  rw [h] at h1
  unfold cleanroomBaseTag litFam at h1
  omega

/-- Quote and literal indices are distinct.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma qIdx_ne_lIdx (m c : ℕ) (lo hi : ℚ) (m' c' r : ℕ) : qIdx m c lo hi ≠ lIdx m' c' r := by
  intro h
  unfold qIdx lIdx freshAtomCode at h
  rw [Nat.pair_eq_pair] at h
  have := h.1
  unfold quoteFam litFam at this
  omega

/-! ## Worlds -/

/-- **The witness world** with price `x`, coordinate flag `b` and literal index `a`: `atom 0`
holds iff `b`; a quote atom holds iff `lo < x < hi`; a literal atom holds iff its index is `a`;
nothing else holds. The dissolution uses `a = 1` in every world (literals decoupled from the
price); `Witness.lean` uses `a` = the cell of `x` (literals linked to the price).
Source: none: witness
Kind: D
Fidelity: n/a -/
def wld (x : ℚ) (b : Bool) (a : ℕ) : PCWorld := fun i =>
  (i = 0 ∧ b = true) ∨ (∃ m c lo hi, i = qIdx m c lo hi ∧ lo < x ∧ x < hi) ∨
    (∃ m c, i = lIdx m c a)

/-- The coordinate in a witness world.
Source: none: witness
Kind: L
Fidelity: n/a -/
@[simp] lemma wld_holds_dPhi (x : ℚ) (b : Bool) (a : ℕ) :
    (wld x b a).Holds dPhi ↔ b = true := by
  show wld x b a 0 ↔ b = true
  constructor
  · rintro (⟨-, hb⟩ | ⟨m, c, lo, hi, h, -, -⟩ | ⟨m, c, h⟩)
    · exact hb
    · exact absurd h.symm (qIdx_ne_zero m c lo hi)
    · exact absurd h.symm (lIdx_ne_zero m c a)
  · intro hb; exact Or.inl ⟨rfl, hb⟩

/-- A quote in a witness world.
Source: none: witness
Kind: L
Fidelity: n/a -/
@[simp] lemma wld_holds_dQuote (x : ℚ) (b : Bool) (a m : ℕ) (φ : Sentence) (lo hi : ℚ) :
    (wld x b a).Holds (dQuote m φ lo hi) ↔ lo < x ∧ x < hi := by
  show wld x b a (qIdx m (Encodable.encode φ) lo hi) ↔ lo < x ∧ x < hi
  constructor
  · rintro (⟨h, -⟩ | ⟨m', c', lo', hi', h, h1, h2⟩ | ⟨m', c', h⟩)
    · exact absurd h (qIdx_ne_zero _ _ _ _)
    · obtain ⟨-, -, rfl, rfl⟩ := qIdx_inj.1 h
      exact ⟨h1, h2⟩
    · exact absurd h (qIdx_ne_lIdx _ _ _ _ _ _ _)
  · intro h; exact Or.inr (Or.inl ⟨m, _, lo, hi, rfl, h.1, h.2⟩)

/-- A literal in a witness world.
Source: none: witness
Kind: L
Fidelity: n/a -/
@[simp] lemma wld_holds_dLit (x : ℚ) (b : Bool) (a m : ℕ) (φ : Sentence) (r : ℕ) :
    (wld x b a).Holds (dLit m φ r) ↔ r = a := by
  show wld x b a (lIdx m (Encodable.encode φ) r) ↔ r = a
  constructor
  · rintro (⟨h, -⟩ | ⟨m', c', lo', hi', h, -, -⟩ | ⟨m', c', h⟩)
    · exact absurd h (lIdx_ne_zero _ _ _)
    · exact absurd h.symm (qIdx_ne_lIdx _ _ _ _ _ _ _)
    · exact (lIdx_inj.1 h).2.2
  · rintro rfl; exact Or.inr (Or.inr ⟨m, _, rfl⟩)

/-! ## Cells, representatives, candidates -/

/-- Lower cell bounds `-1`, `1/4` (`bli-found`'s `halfLo`).
Source: none: witness
Kind: D
Fidelity: n/a -/
def dLo (_m r : ℕ) : ℚ := if r = 0 then -1 else 1 / 4

/-- Upper cell bounds `1/2`, `2` (`halfHi`).
Source: none: witness
Kind: D
Fidelity: n/a -/
def dHi (_m r : ℕ) : ℚ := if r = 0 then 1 / 2 else 2

/-- Representatives `1/4`, `3/4` (`witnessRep`).
Source: none: witness
Kind: D
Fidelity: n/a -/
def dRep (_m r : ℕ) : ℚ := if r = 0 then 1 / 4 else 3 / 4

/-- Two cells.
Source: none: witness
Kind: D
Fidelity: n/a -/
def dCells (_m : ℕ) : Finset ℕ := {0, 1}

/-- The candidate table assigning the coordinate the cell `r`, coded.
Source: none: witness
Kind: D
Fidelity: n/a -/
def dCode (r : ℕ) : ℕ := Encodable.encode [(dC0, r)]

/-- `dCode` is injective.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma dCode_inj {r r' : ℕ} : dCode r = dCode r' ↔ r = r' := by
  unfold dCode
  rw [Encodable.encode_inj]
  simp

/-- `dCode 0 ≠ dCode 1`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma dCode_zero_ne_one : dCode 0 ≠ dCode 1 := fun h => by simpa using dCode_inj.1 h

/-- The table of `dCode r`.
Source: none: witness
Kind: L
Fidelity: n/a -/
@[simp] lemma tableOfCode_dCode (r : ℕ) : tableOfCode (dCode r) = [(dC0, r)] := by
  unfold dCode; exact tableOfCode_encode _

/-- The two candidates, every day.
Source: none: witness
Kind: D
Fidelity: n/a -/
def dStates (_m : ℕ) : Finset ℕ := {dCode 0, dCode 1}

/-- Membership in `dStates`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma mem_dStates {m q : ℕ} : q ∈ dStates m ↔ q = dCode 0 ∨ q = dCode 1 := by
  simp [dStates]

/-- The witness's state family: the interval state sentence over `dQuote`.
Source: none: witness
Kind: D
Fidelity: n/a -/
abbrev dσ : ℕ → ℕ → Sentence := intervalState dQuote dLo dHi

/-- The state sentence of `dCode r` is the open-cell quote of the coordinate (conjoined with `⊤`).
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma dσ_dCode (m r : ℕ) : dσ m (dCode r) = dQuote m dPhi (dLo m r) (dHi m r) ⋏ ⊤ := by
  simp [intervalState, conjList]

/-- A witness world holds the state sentence of `dCode r` iff its price lies in cell `r`.
Source: none: witness
Kind: L
Fidelity: n/a -/
@[simp] lemma wld_holds_dσ (x : ℚ) (b : Bool) (a m r : ℕ) :
    (wld x b a).Holds (dσ m (dCode r)) ↔ dLo m r < x ∧ x < dHi m r := by
  rw [dσ_dCode, PCWorld.holds_and, wld_holds_dQuote]
  exact ⟨fun h => h.1, fun h => ⟨h, PCWorld.holds_top _⟩⟩

/-! ## Payouts of the witness worlds -/

/-- Payout of a state sentence when the price is in the cell.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma payout_dσ_of_mem {x : ℚ} {m r : ℕ} (h : dLo m r < x ∧ x < dHi m r) (b : Bool) (a : ℕ) :
    (wld x b a).payout (dσ m (dCode r)) = 1 :=
  payout_of_holds ((wld_holds_dσ x b a m r).2 h)

/-- Payout of a state sentence when the price is outside the cell.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma payout_dσ_of_not_mem {x : ℚ} {m r : ℕ} (h : ¬ (dLo m r < x ∧ x < dHi m r)) (b : Bool)
    (a : ℕ) : (wld x b a).payout (dσ m (dCode r)) = 0 :=
  payout_of_not_holds fun h' => h ((wld_holds_dσ x b a m r).1 h')

/-- Payout of the coordinate: the flag.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma payout_dPhi_true (x : ℚ) (a : ℕ) : (wld x true a).payout dPhi = 1 :=
  payout_of_holds ((wld_holds_dPhi x true a).2 rfl)

/-- See `payout_dPhi_true`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma payout_dPhi_false (x : ℚ) (a : ℕ) : (wld x false a).payout dPhi = 0 :=
  payout_of_not_holds fun h => Bool.false_ne_true ((wld_holds_dPhi x false a).1 h)

/-- Payout of the world's own literal: `1`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma payout_dLit_self (x : ℚ) (b : Bool) (a m : ℕ) (φ : Sentence) :
    (wld x b a).payout (dLit m φ a) = 1 :=
  payout_of_holds ((wld_holds_dLit x b a m φ a).2 rfl)

/-- Payout of any other literal: `0`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma payout_dLit_ne (x : ℚ) (b : Bool) {a r : ℕ} (h : r ≠ a) (m : ℕ) (φ : Sentence) :
    (wld x b a).payout (dLit m φ r) = 0 :=
  payout_of_not_holds fun h' => h ((wld_holds_dLit x b a m φ r).1 h')

/-- The prices `1/8`, `7/8` lie in cells `0`, `1` respectively, and in no other.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma cell_facts (m : ℕ) :
    (dLo m 0 < 1 / 8 ∧ (1 / 8 : ℚ) < dHi m 0) ∧ ¬ (dLo m 1 < 1 / 8 ∧ (1 / 8 : ℚ) < dHi m 1) ∧
      ¬ (dLo m 0 < 7 / 8 ∧ (7 / 8 : ℚ) < dHi m 0) ∧ (dLo m 1 < 7 / 8 ∧ (7 / 8 : ℚ) < dHi m 1) := by
  norm_num [dLo, dHi]

/-! ## The four worlds and the mixture -/

/-- The four worlds: price `1/8` (cell `0`) or `7/8` (cell `1`), coordinate true or false.
Source: none: witness
Kind: D
Fidelity: n/a -/
def dWorld : Fin 4 → PCWorld
  | 0 => wld (1 / 8) true 1
  | 1 => wld (1 / 8) false 1
  | 2 => wld (7 / 8) true 1
  | 3 => wld (7 / 8) false 1

/-- The weights `1/8, 3/8, 3/8, 1/8`.
Source: none: witness
Kind: D
Fidelity: n/a -/
noncomputable def dW : Fin 4 → ℝ
  | 0 => 1 / 8
  | 1 => 3 / 8
  | 2 => 3 / 8
  | 3 => 1 / 8

/-- Every world of the mixture is a witness world with price in `(-1, 2)`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma dWorld_eq (i : Fin 4) : ∃ (x : ℚ) (b : Bool), -1 < x ∧ x < 2 ∧ dWorld i = wld x b 1 :=
  match i with
  | 0 => ⟨1 / 8, true, by norm_num, by norm_num, rfl⟩
  | 1 => ⟨1 / 8, false, by norm_num, by norm_num, rfl⟩
  | 2 => ⟨7 / 8, true, by norm_num, by norm_num, rfl⟩
  | 3 => ⟨7 / 8, false, by norm_num, by norm_num, rfl⟩

/-- The weights are nonnegative.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma dW_nonneg (i : Fin 4) : 0 ≤ dW i :=
  match i with
  | 0 => by norm_num [dW]
  | 1 => by norm_num [dW]
  | 2 => by norm_num [dW]
  | 3 => by norm_num [dW]

/-- The weights sum to one.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma dW_sum : ∑ i, dW i = 1 := by
  simp [Fin.sum_univ_four, dW]; norm_num

/-- **The witness market**: the same four-world mixture on every day.
Source: none: witness
Kind: D
Fidelity: n/a -/
noncomputable def dP : History := fun _ φ => ∑ i : Fin 4, dW i * (dWorld i).payout φ

/-- `dP` unfolded over the four worlds.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma dP_eq (n : ℕ) (φ : Sentence) :
    dP n φ = 1 / 8 * (wld (1 / 8) true 1).payout φ + 3 / 8 * (wld (1 / 8) false 1).payout φ +
      3 / 8 * (wld (7 / 8) true 1).payout φ + 1 / 8 * (wld (7 / 8) false 1).payout φ := by
  simp [dP, Fin.sum_univ_four, dW, dWorld]

/-- The state masses: each candidate has mass `1/2`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma dP_state (n m : ℕ) : dP n (dσ m (dCode 0)) = 1 / 2 ∧ dP n (dσ m (dCode 1)) = 1 / 2 := by
  obtain ⟨h00, h01, h10, h11⟩ := cell_facts m
  constructor
  · rw [dP_eq, payout_dσ_of_mem h00, payout_dσ_of_mem h00, payout_dσ_of_not_mem h10,
      payout_dσ_of_not_mem h10]
    norm_num
  · rw [dP_eq, payout_dσ_of_not_mem h01, payout_dσ_of_not_mem h01, payout_dσ_of_mem h11,
      payout_dσ_of_mem h11]
    norm_num

/-- The coordinate's price is `1/2`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma dP_dPhi (n : ℕ) : dP n dPhi = 1 / 2 := by
  rw [dP_eq, payout_dPhi_true, payout_dPhi_false, payout_dPhi_true, payout_dPhi_false]
  norm_num

/-- The literal prices: `0` at cell `0`, `1` at cell `1`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma dP_dLit (n m : ℕ) (φ : Sentence) :
    dP n (dLit m φ 0) = 0 ∧ dP n (dLit m φ 1) = 1 := by
  have h01 : (0 : ℕ) ≠ 1 := by norm_num
  constructor
  · rw [dP_eq, payout_dLit_ne _ _ h01, payout_dLit_ne _ _ h01, payout_dLit_ne _ _ h01,
      payout_dLit_ne _ _ h01]
    norm_num
  · rw [dP_eq, payout_dLit_self, payout_dLit_self, payout_dLit_self, payout_dLit_self]; norm_num

/-! ## The state system -/

/-- **The witness's values: the conditional probability given the state.** On `dCode 0` the
conditional of the two cell-`0` worlds, on `dCode 1` of the two cell-`1` worlds (each state has
mass `1/2`, hence the factor `2`); `0` on any other code.
Source: none: witness
Kind: D
Fidelity: n/a -/
noncomputable def dVal (_m q : ℕ) (φ : Sentence) : ℝ :=
  if q = dCode 0 then
    2 * (1 / 8 * (wld (1 / 8) true 1).payout φ + 3 / 8 * (wld (1 / 8) false 1).payout φ)
  else if q = dCode 1 then
    2 * (3 / 8 * (wld (7 / 8) true 1).payout φ + 1 / 8 * (wld (7 / 8) false 1).payout φ)
  else 0

/-- The witness state system: two candidates a day, conditional values, realized state `dCode 1`.
Source: none: witness
Kind: D
Fidelity: n/a -/
noncomputable def dS : StateSystem where
  states := dStates
  val := dVal
  actual _ := dCode 1
  actual_mem _ := by simp [dStates]

/-- `dS.states`.
Source: none: witness
Kind: L
Fidelity: n/a -/
@[simp] lemma dS_states : dS.states = dStates := rfl

/-- `dS.val`.
Source: none: witness
Kind: L
Fidelity: n/a -/
@[simp] lemma dS_val : dS.val = dVal := rfl

/-- `dVal` at `dCode 0`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma dVal_zero (m : ℕ) (φ : Sentence) : dVal m (dCode 0) φ =
    2 * (1 / 8 * (wld (1 / 8) true 1).payout φ + 3 / 8 * (wld (1 / 8) false 1).payout φ) := by
  rw [dVal, if_pos rfl]

/-- `dVal` at `dCode 1`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma dVal_one (m : ℕ) (φ : Sentence) : dVal m (dCode 1) φ =
    2 * (3 / 8 * (wld (7 / 8) true 1).payout φ + 1 / 8 * (wld (7 / 8) false 1).payout φ) := by
  rw [dVal, if_neg dCode_zero_ne_one.symm, if_pos rfl]

/-- The values at the coordinate are the representatives.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma dVal_dPhi (m : ℕ) : dVal m (dCode 0) dPhi = 1 / 4 ∧ dVal m (dCode 1) dPhi = 3 / 4 := by
  constructor
  · rw [dVal_zero, payout_dPhi_true, payout_dPhi_false]; norm_num
  · rw [dVal_one, payout_dPhi_true, payout_dPhi_false]; norm_num

/-! ## The process -/

/-- The day-`k` stage: the default-cell quotes of every `m ≤ k` and every `φ` small on day `k`.
Source: none: witness
Kind: D
Fidelity: n/a -/
noncomputable def dStage (k : ℕ) : Finset Sentence :=
  ((Finset.range (k + 1)) ×ˢ smallSet k).image fun p => dQuote p.1 p.2 (-1) 2

/-- The stages are nested.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma dStage_mono (k : ℕ) : dStage k ⊆ dStage (k + 1) := by
  intro ψ hψ
  unfold dStage at hψ ⊢
  rw [Finset.mem_image] at hψ ⊢
  obtain ⟨p, hp, rfl⟩ := hψ
  refine ⟨p, ?_, rfl⟩
  rw [Finset.mem_product] at hp ⊢
  exact ⟨Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 hp.1)),
    smallSet_mono (Nat.le_succ k) hp.2⟩

/-- **The witness process**: by day `k`, the default-cell quotes `dQuote m φ (-1) 2` of every
`m ≤ k` and every `φ` small on day `k`. It decides no price.
Source: none: witness (so that `LNKcell` holds at unlisted coordinates)
Kind: D
Fidelity: n/a -/
noncomputable def dDP : DeductiveProcess where
  D := dStage
  mono := dStage_mono

/-- Membership in a stage of `dDP`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma mem_dDP {k : ℕ} {ψ : Sentence} :
    ψ ∈ dDP.D k ↔ ∃ m ≤ k, ∃ φ ∈ smallSet k, ψ = dQuote m φ (-1) 2 := by
  show ψ ∈ dStage k ↔ _
  unfold dStage
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists]
  constructor
  · rintro ⟨m, φ, ⟨hm, hφ⟩, h⟩
    exact ⟨m, Nat.lt_succ_iff.1 hm, φ, hφ, h.symm⟩
  · rintro ⟨m, hm, φ, hφ, h⟩
    exact ⟨m, φ, ⟨Nat.lt_succ_iff.2 hm, hφ⟩, h.symm⟩

/-- A witness world with price in `(-1, 2)` is consistent with the completed theory of `dDP`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma wld_consistentWithTheory {x : ℚ} (h1 : -1 < x) (h2 : x < 2) (b : Bool) (a : ℕ) :
    (wld x b a).ConsistentWithTheory dDP := by
  intro k ψ hψ
  obtain ⟨m, -, φ, -, rfl⟩ := mem_dDP.1 hψ
  exact (wld_holds_dQuote x b a _ _ _ _).2 ⟨h1, h2⟩

/-- Every one of the four worlds is consistent with the completed theory of `dDP`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma dWorld_consistentWithTheory (i : Fin 4) : (dWorld i).ConsistentWithTheory dDP := by
  obtain ⟨x, b, h1, h2, h⟩ := dWorld_eq i
  rw [h]; exact wld_consistentWithTheory h1 h2 b 1

/-- Every witness world has interval semantics.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma wld_intervalSem (x : ℚ) (b : Bool) (a : ℕ) : IntervalSem dQuote (wld x b a) where
  mono := by
    intro m φ lo hi lo' hi' hlo hhi h
    rw [wld_holds_dQuote] at h ⊢
    exact ⟨lt_trans hlo h.1, lt_trans h.2 hhi⟩
  meet := by
    intro m φ lo hi lo' hi' h h'
    rw [wld_holds_dQuote] at h h'
    exact le_trans (max_le h.1.le h'.1.le) (le_min h.2.le h'.2.le)

/-- The cell `cellOfTable dLo dHi` assigns: the entry's cell at the coordinate, the default
elsewhere.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma cellOfTable_dCode (m r : ℕ) (φ : Sentence) :
    cellOfTable dLo dHi m (dCode r) φ =
      if Encodable.encode φ = dC0 then (dLo m r, dHi m r) else (-1, 2) := by
  unfold cellOfTable
  rw [tableOfCode_dCode]
  by_cases h : Encodable.encode φ = dC0
  · simp [entryOf, h]
  · simp [entryOf, h, Ne.symm h]

/-- A sentence whose code is `dC0` is `dPhi`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma eq_dPhi_of_encode {φ : Sentence} (h : Encodable.encode φ = dC0) : φ = dPhi := by
  have := congrArg sentenceOfCode h
  rwa [sentenceOfCode_encode, sentenceOfCode_dC0] at this

/-- **Every witness world with price in `(-1, 2)` is linked** on every day: the state sentence
of `dCode r` forces the quote of the cell it assigns the coordinate (its own conjunct) and the
default quote elsewhere.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma wld_linkedWorld {x : ℚ} (h1 : -1 < x) (h2 : x < 2) (b : Bool) (a m : ℕ) :
    LinkedWorld dσ dQuote dS (cellOfTable dLo dHi) m (wld x b a) := by
  intro q hq φ _ hs
  rw [dS_states, mem_dStates] at hq
  rcases hq with rfl | rfl <;>
  · rw [cellOfTable_dCode]
    rw [wld_holds_dσ] at hs
    by_cases h : Encodable.encode φ = dC0
    · rw [if_pos h]; exact (wld_holds_dQuote _ _ _ _ _ _ _).2 hs
    · rw [if_neg h]; exact (wld_holds_dQuote _ _ _ _ _ _ _).2 ⟨h1, h2⟩

/-! ## The package -/

/-- **`LNKcell` holds**: every completed-theory world of `dDP` is linked (the listed coordinate
propositionally; the unlisted ones through the stage's default quotes).
Source: mandate § Attempt angles (B)
Kind: L
Fidelity: n/a -/
theorem dLNKcell : LNKcell dσ dQuote dS (cellOfTable dLo dHi) dDP := by
  intro m q hq φ hφ v hv hs
  rw [dS_states, mem_dStates] at hq
  have hdef : v.Holds (dQuote m φ (-1) 2) := hv m _ (mem_dDP.2 ⟨m, le_rfl, φ, hφ, rfl⟩)
  rcases hq with rfl | rfl <;>
  · rw [cellOfTable_dCode]
    by_cases h : Encodable.encode φ = dC0
    · rw [if_pos h, eq_dPhi_of_encode h]
      rw [dσ_dCode, PCWorld.holds_and] at hs
      exact hs.1
    · rw [if_neg h]; exact hdef

/-- **`PCPσTheory` holds** (for every atom set): `dP n` is by definition the four-world mixture,
and each world is consistent with the completed theory.
Source: mandate § Attempt angles (B)
Kind: L
Fidelity: n/a -/
theorem dPCPσTheory (atoms : ℕ → Finset ℕ) : PCPσTheory atoms dDP dP :=
  fun _ => ⟨4, dWorld, dW, dWorld_consistentWithTheory, dW_nonneg, dW_sum, fun _ _ => rfl⟩

/-- **`PCPσLinked` holds** (for every atom set): each world is stage-consistent, linked, and has
interval semantics.
Source: mandate § Attempt angles (B)
Kind: L
Fidelity: n/a -/
theorem dPCPσLinked (atoms : ℕ → Finset ℕ) :
    PCPσLinked dσ dQuote dS (cellOfTable dLo dHi) atoms dDP dP := by
  intro n
  refine ⟨4, dWorld, dW, fun i => ⟨dWorld_consistentWithTheory i n, ?_, ?_⟩,
    dW_nonneg, dW_sum, fun _ _ => rfl⟩
  · obtain ⟨x, b, h1, h2, h⟩ := dWorld_eq i
    rw [h]; exact wld_linkedWorld h1 h2 b 1 _
  · obtain ⟨x, b, -, -, h⟩ := dWorld_eq i
    rw [h]; exact wld_intervalSem x b 1

/-- **`E1x` holds** with the base `dP` itself.
Source: mandate § Attempt angles (B)
Kind: L
Fidelity: n/a -/
theorem dE1x : E1x dP dP := fun _ _ _ => rfl

/-- **`E5σ` holds**: masses `1/2 + 1/2`, and no world has its price in both cells.
Source: mandate § Attempt angles (B)
Kind: L
Fidelity: n/a -/
theorem dE5σ : E5σ dσ dS dP := by
  intro n
  obtain ⟨h00, h01, h10, h11⟩ := cell_facts (n + 1)
  have hex : ∀ b : Bool, ∀ x : ℚ, (x = 1 / 8 ∨ x = 7 / 8) →
      (wld x b 1).payout (dσ (n + 1) (dCode 0) ⋏ dσ (n + 1) (dCode 1)) = 0 := by
    rintro b x (rfl | rfl)
    · rw [payout_and, payout_dσ_of_not_mem h01, mul_zero]
    · rw [payout_and, payout_dσ_of_not_mem h10, zero_mul]
  constructor
  · rw [dS_states, dStates, Finset.sum_pair dCode_zero_ne_one, (dP_state n (n + 1)).1,
      (dP_state n (n + 1)).2]
    norm_num
  · intro q₁ hq₁ q₂ hq₂ hne
    rw [dS_states, mem_dStates] at hq₁ hq₂
    rcases hq₁ with rfl | rfl <;> rcases hq₂ with rfl | rfl
    · exact absurd rfl hne
    · rw [dP_eq, hex _ _ (Or.inl rfl), hex _ _ (Or.inl rfl), hex _ _ (Or.inr rfl),
        hex _ _ (Or.inr rfl)]
      norm_num
    · have hex' : ∀ b : Bool, ∀ x : ℚ, (x = 1 / 8 ∨ x = 7 / 8) →
          (wld x b 1).payout (dσ (n + 1) (dCode 1) ⋏ dσ (n + 1) (dCode 0)) = 0 := by
        rintro b x (rfl | rfl)
        · rw [payout_and, payout_dσ_of_not_mem h01, zero_mul]
        · rw [payout_and, payout_dσ_of_not_mem h10, mul_zero]
      rw [dP_eq, hex' _ _ (Or.inl rfl), hex' _ _ (Or.inl rfl), hex' _ _ (Or.inr rfl),
        hex' _ _ (Or.inr rfl)]
      norm_num
    · exact absurd rfl hne

/-- **`E2xσ` holds, at every sentence** (not only on `Sminus`): faith is conditioning.
Source: mandate § Attempt angles (B); bli-found F-12 (faith as conditioning in product form)
Kind: L
Fidelity: n/a -/
theorem dE2xσ : E2xσ dσ dS dP := by
  intro n m _ q hq φ _
  obtain ⟨h00, h01, h10, h11⟩ := cell_facts m
  rw [dS_states, mem_dStates] at hq
  rcases hq with rfl | rfl
  · rw [dP_eq, dP_eq, dS_val, dVal_zero]
    simp only [payout_and, payout_dσ_of_mem h00, payout_dσ_of_not_mem h10]
    ring
  · rw [dP_eq, dP_eq, dS_val, dVal_one]
    simp only [payout_and, payout_dσ_of_not_mem h01, payout_dσ_of_mem h11]
    ring

/-! ## The cell family and the violation -/

/-- The witness's cell family over the witness worlds: literals `dLit`, cells `{0, 1}`,
representatives `1/4, 3/4`; exclusive and exhaustive in every witness world (exactly the
index-`1` literal holds).
Source: mandate § Definitions (`CellFamily`)
Kind: D
Fidelity: n/a -/
noncomputable def dCF : CellFamily (fun v => ∃ (x : ℚ) (b : Bool), v = wld x b 1) where
  literal := dLit
  cells := dCells
  rep := dRep
  excl := by
    rintro m φ r r' hne v ⟨x, b, rfl⟩ ⟨h, h'⟩
    rw [wld_holds_dLit] at h h'
    exact hne (h.trans h'.symm)
  exh := by
    rintro m φ v ⟨x, b, rfl⟩
    exact ⟨1, by simp [dCells], (wld_holds_dLit x b 1 m φ 1).2 rfl⟩

/-- `dCF.literal`.
Source: none: witness
Kind: L
Fidelity: n/a -/
@[simp] lemma dCF_literal : dCF.literal = dLit := rfl

/-- `dCF.cells`.
Source: none: witness
Kind: L
Fidelity: n/a -/
@[simp] lemma dCF_cells : dCF.cells = dCells := rfl

/-- `dCF.rep`.
Source: none: witness
Kind: L
Fidelity: n/a -/
@[simp] lemma dCF_rep : dCF.rep = dRep := rfl

/-- The index lists codes.
Source: none: witness
Kind: L
Fidelity: n/a -/
theorem dIndexCodes (m : ℕ) : IndexCodes dIndex m := by
  intro c hc
  simp only [dIndex, List.mem_singleton] at hc
  subst hc
  rw [sentenceOfCode_dC0]
  rfl

/-- Every candidate values the coordinate at the representative of the cell it lists.
Source: mandate K2 (`hval`)
Kind: L
Fidelity: n/a -/
theorem dValuesAtRep (n : ℕ) : ValuesAtRep dCF dS dIndex n := by
  intro q hq c hc
  simp only [dIndex, List.mem_singleton] at hc
  subst hc
  rw [dS_states, mem_dStates] at hq
  rcases hq with rfl | rfl
  · refine ⟨0, by simp [dCells], by simp [entryOf], ?_⟩
    rw [dS_val, sentenceOfCode_dC0, (dVal_dPhi (n + 1)).1, dCF_rep, dRep]
    norm_num
  · refine ⟨1, by simp [dCells], by simp [entryOf], ?_⟩
    rw [dS_val, sentenceOfCode_dC0, (dVal_dPhi (n + 1)).2, dCF_rep, dRep]
    norm_num

/-- The literal family at the coordinate is machine-metered (an atom family over a
`Nat.pair`-nest of the day and constants), hence eventually day-small.
Source: bli-leak `machineSentenceCodes_atom_of_machineDigits` (re-proved inline); bli-found `Emitter.machineSentenceCodes_eventually_small`
Kind: L
Fidelity: n/a -/
theorem dLit_eventually_small (r : ℕ) : ∃ N, ∀ n ≥ N, SmallOn n (dLit (n + 1) dPhi r) := by
  have hd : MachineDigits fun n => lIdx (n + 1) dC0 r :=
    (MachineDigits.natPair (MachineDigits.const (cleanroomBaseTag + litFam))
      (MachineDigits.natPair ((MachineDigits.ofUnaryRuler UnaryRuler.id).add (MachineDigits.const 1))
        (MachineDigits.const (Nat.pair dC0 r)))).of_eq (fun _ => rfl)
  have hm : MachineSentenceCodes fun n => dLit (n + 1) dPhi r :=
    MachineSentenceCodes.ofCanonical
      (MachineTokenStream.of_eq (hd.add (MachineDigits.const 5)) (fun _ => rfl))
  exact machineSentenceCodes_eventually_small hm

/-- **The pinned set is eventually non-empty**: from some day on, the coordinate's two cell
literals are small.
Source: mandate K1 (pinned set non-empty); [[bli-program-desiderata]] §10 item 10
Kind: L
Fidelity: n/a -/
theorem pinned_eventually : ∃ N, ∀ n ≥ N, dC0 ∈ pinned dCF dIndex n := by
  obtain ⟨N₀, h₀⟩ := dLit_eventually_small 0
  obtain ⟨N₁, h₁⟩ := dLit_eventually_small 1
  refine ⟨max N₀ N₁, fun n hn => ?_⟩
  rw [mem_pinned]
  refine ⟨by simp [dIndex], fun r hr => ?_⟩
  rw [dCF_cells, dCells, Finset.mem_insert, Finset.mem_singleton] at hr
  rw [dCF_literal, sentenceOfCode_dC0]
  rcases hr with rfl | rfl
  · exact h₀ n (le_trans (le_max_left _ _) hn)
  · exact h₁ n (le_trans (le_max_right _ _) hn)

/-- **The base violates `D_NNUcell`**: at every pinned day, `dP n φ₀ = 1/2` but
`∑_r rep_r · dP n (lit_r) = 1/4 · 0 + 3/4 · 1 = 3/4`.
Source: mandate § Attempt angles (B: "a base `Q` that violates the exact `D_NNUcell`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem dNot_D_NNUcell : ¬ D_NNUcell dCF dIndex dP := by
  intro h
  obtain ⟨N, hN⟩ := pinned_eventually
  have := h N dC0 (hN N le_rfl)
  rw [sentenceOfCode_dC0, dP_dPhi, dCF_cells, dCells, dCF_literal, dCF_rep,
    Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1), (dP_dLit N (N + 1) dPhi).1,
    (dP_dLit N (N + 1) dPhi).2] at this
  norm_num [dRep] at this

/-- **Dissolution (angle B's headline negative result).** Over the process `dDP`, the interval
state family `dσ`, the state system `dS` and the market `dP := Q`, the full linked package holds —
`LNKcell`, `PCPσTheory` (hence `PCPσ`), `PCPσLinked`, `E5σ`, `E1x`, `E2xσ` — the pinned set is
non-empty from some day on, and yet `D_NNUcell` fails. Under interval-only linkage the exact
no-net-update identity is not forced; the trilemma in its `D_NNUcell` form dissolves, and what
remains is the bracket LP (`Bracket.lean`). Contrast `Determination.d_nnucell_of_package`: with
the B2 state sentence (the cell-literal conjunction) the identity *is* forced, by propositional
means, at the stage level. The two theorems together are the answer to the mandate's decisive
question: whether the trilemma survives depends on whether the state sentence entails the cell
literals, not on which linkage is used.
Source: mandate § Attempt angles (B); [[bli-program]] §3.6(ii); [[bli-program-desiderata]] I6
Kind: N+
Fidelity: exact (abstract process and quote family: the quotes are atoms the theory does not tie to a price)
Hyps: (a) -/
theorem dissolution :
    LNKcell dσ dQuote dS (cellOfTable dLo dHi) dDP ∧
      PCPσTheory (stateAtoms dσ dS) dDP dP ∧
      PCPσLinked dσ dQuote dS (cellOfTable dLo dHi) (stateAtoms dσ dS) dDP dP ∧
      E5σ dσ dS dP ∧ E1x dP dP ∧ E2xσ dσ dS dP ∧
      (∃ N, ∀ n ≥ N, dC0 ∈ pinned dCF dIndex n) ∧
      ¬ D_NNUcell dCF dIndex dP :=
  ⟨dLNKcell, dPCPσTheory _, dPCPσLinked _, dE5σ, dE1x, dE2xσ, pinned_eventually, dNot_D_NNUcell⟩

/-- **N+ grade of the witness**: two candidates with distinct tables, each charged `1/2`; the
base is uncertain about the coordinate (`1/2`) and about its next-day cell.
Source: mandate K2 (witness grades: "≥ 2 states charged, distinct tables, `d ≥ 2` cells")
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem dissolution_nondegenerate (n : ℕ) :
    dCode 0 ≠ dCode 1 ∧ 0 < dP n (dσ (n + 1) (dCode 0)) ∧ 0 < dP n (dσ (n + 1) (dCode 1)) ∧
      (dCells (n + 1)).card = 2 ∧ dP n dPhi = 1 / 2 := by
  refine ⟨dCode_zero_ne_one, ?_, ?_, by simp [dCells], dP_dPhi n⟩
  · rw [(dP_state n (n + 1)).1]; norm_num
  · rw [(dP_state n (n + 1)).2]; norm_num

end Dissolve

end Cleanroom.Bli.BliLinkageB
