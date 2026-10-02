import Cleanroom.Bli.BliLinkage.AttemptA.Determination
import Cleanroom.Bli.BliFound.Grid

/-!
# `bli-linkage`, attempt A — the B2 instance over FAF's `paperDP 𝗜𝚺₁`

The abstract family of `Defs.lean` instantiated at `bli-found`'s B2 encoding: `cellLit :=
cellSentence T round hround` (FAF's tag-`2` quotation atoms), exclusivity/exhaustiveness from
`cellSentence_reflected` and the rounding being total into the grid (`b2Family`); `stateOf` is
`stateSentence` by `rfl` (`stateOf_eq_stateSentence`). At `𝗜𝚺₁` with `halfRound` (two cells at
`1/2`), the four-table grid `fixedStates` over `[⌜⊥⌝, ⌜⊤⌝]` with the **endpoint representatives**
`rep01 = (0, 1)` (`fixedSystem01`) is `Tabular` (`fixedSystem01_tabular`); K1 and K2 are
instantiated (`forced_marginal_B2`, `determination_B2`); the **pinned set is eventually
non-empty** — both `⌜⊥⌝` and `⌜⊤⌝` are pinned from some day `N` on (`exists_pinned_from`), by
the size bound `tokenSize (atom a) ≤ log₄ a + 3` and a `Nat.pair`-polynomial bound on the
quotation atom's index (the quote code's constant is opaque, so `∃ N`, no numeral); and the
scope condition of `determination` holds (`scope_witnessIndex`).

**Why the endpoint representatives.** `bli-found`'s `witnessRep = (1/4, 3/4)` cannot carry
faith: `⊥ ∈ Sminus m m` always, coherence gives `P n (⊥ ⋏ σ_q) = 0`, and faith demands
`val q ⊥ · P n σ_q = 1/4 · P n σ_q` — so every charged state dies and `E5σ` fails
(`witnessRep_faith_unsat`). With `rep01` the decided coordinates `⊥`, `⊤` have faith values
`0`, `1`, consistent with coherence. Findings F-A2.

**`E2xσ` is unsatisfiable over the list-table system anyway** (`fixedSystem01_e2xσ_unsat`,
from the general `e2xσ_unsat_of_unlisted_tautology`): the scope `Sminus m m` contains the
unlisted tautology `⊤ ⋏ ⊤` from `m = 2`, whose value in every table is the junk `0`. This is why
K2 is stated at `E2xσIdx`. Findings F-A1.
-/

namespace Cleanroom.Bli.BliLinkage.AttemptA

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliTrajectory

open Classical

namespace B2

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]

/-! ## The B2 family -/

/-- **The B2 cell family** over `paperDP T`: literals `cellSentence T round hround`, an abstract
grid `cells` the rounding is total into, representatives `rep`. Exclusivity and exhaustiveness
are `cellSentence_reflected` (the literal holds iff the rounded quote *is* `r`).
Source: mandate § Definitions ("B2 instance: `lit := cellSentence …`, `excl`/`exh` from
`cellSentence_reflected` and `round` being a total function into `cells`")
Kind: D
Fidelity: exact -/
noncomputable def b2Family (round : ℕ → ℚ → ℕ) (hround : Computable fun p : ℕ × ℚ => round p.1 p.2)
    (cells : ℕ → Finset ℕ) (hcells : ∀ m x, round m x ∈ cells m) (rep : ℕ → ℕ → ℚ) :
    CellFamily (paperDP T) where
  cellLit := cellSentence T round hround
  cells := cells
  rep := rep
  excl := by
    intro m c r r' hne v hv ⟨h1, h2⟩
    rw [cellSentence_reflected T round hround m c r v hv] at h1
    rw [cellSentence_reflected T round hround m c r' v hv] at h2
    exact hne (h1.symm.trans h2)
  exh := fun m c v hv => ⟨round m (marketValue T (Nat.pair m c)), hcells _ _,
    (cellSentence_reflected T round hround m c _ v hv).2 rfl⟩

/-- **`stateOf` at B2 is `stateSentence`, definitionally.**
Source: mandate § Definitions (`stateOf_eq_stateSentence`)
Kind: L
Fidelity: exact -/
theorem stateOf_eq_stateSentence (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (cells : ℕ → Finset ℕ)
    (hcells : ∀ m x, round m x ∈ cells m) (rep : ℕ → ℕ → ℚ) (m q : ℕ) :
    stateOf (b2Family T round hround cells hcells rep) m q = stateSentence T round hround m q := rfl

/-! ## `halfRound` at `𝗜𝚺₁`, endpoint representatives, the four-table grid -/

/-- The endpoint representatives: cell `0 ↦ 0`, cell `1 ↦ 1`.
Source: this run (see the module docstring; mandate K4c "faith at `⊥`/`⊤` is `0`/`1`")
Kind: D
Fidelity: exact -/
def rep01 (_m r : ℕ) : ℚ := if r = 0 then 0 else 1

/-- `halfRound` is total into `{0, 1}`.
Source: none: infrastructure (`halfRound_le_one`)
Kind: L
Fidelity: n/a -/
lemma halfRound_mem_cells (m : ℕ) (x : ℚ) : halfRound m x ∈ ({0, 1} : Finset ℕ) := by
  have := halfRound_le_one m x
  simp only [Finset.mem_insert, Finset.mem_singleton]; omega

/-- **The family of record at `𝗜𝚺₁`**: `halfRound`, cells `{0, 1}`, representatives `rep01`.
Source: mandate § K1 (witness: `𝗜𝚺₁`, `halfRound`)
Kind: D
Fidelity: exact -/
noncomputable def halfFamily : CellFamily (paperDP 𝗜𝚺₁) :=
  b2Family 𝗜𝚺₁ halfRound halfRound_computable (fun _ => {0, 1}) (fun m x => halfRound_mem_cells m x)
    rep01

/-- **The four-table system with endpoint representatives**: `bli-found`'s `fixedStates` over
`[⌜⊥⌝, ⌜⊤⌝]` as a `b2StateSystem` with `rep01`.
Source: mandate § K1 (witness: `Grid.fixedSystem`), with `rep01` in place of `witnessRep` (module docstring)
Kind: D
Fidelity: exact -/
noncomputable def fixedSystem01 : StateSystem :=
  b2StateSystem 𝗜𝚺₁ halfRound witnessIndex fixedStates actualCode_mem_fixedStates rep01

/-- The entry of a fixed table at `⌜⊥⌝` is its first index, at `⌜⊤⌝` its second.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma entryOf_tbl (a b : ℕ) :
    entryOf (Encodable.encode (⊥ : Sentence)) (tbl a b) = some a ∧
      entryOf (Encodable.encode (⊤ : Sentence)) (tbl a b) = some b := by
  have hne : Encodable.encode (⊤ : Sentence) ≠ Encodable.encode (⊥ : Sentence) := by
    intro h; have := Encodable.encode_inj.1 h; cases this
  simp [tbl, entryOf]

/-- **The four-table system is `Tabular`** over the family of record.
Source: mandate § K2 (`hval` "discharged at B2 by `rfl`"), § K5a ("tables over `index (n+1)`")
Kind: L
Fidelity: exact -/
theorem fixedSystem01_tabular : Tabular halfFamily witnessIndex fixedSystem01 where
  keys := by
    intro m q hq c hc
    simp only [fixedSystem01, b2StateSystem, fixedStates, Finset.mem_insert,
      Finset.mem_singleton] at hq
    simp only [witnessIndex, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hq with rfl | rfl | rfl | rfl <;> rcases hc with rfl | rfl <;> rw [tableOfCode_encode] <;>
      first
        | exact ⟨_, by simp [halfFamily, b2Family], (entryOf_tbl _ _).1⟩
        | exact ⟨_, by simp [halfFamily, b2Family], (entryOf_tbl _ _).2⟩
  val := by
    intro m q _ c hc r he
    simp only [witnessIndex, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
    · simp only [fixedSystem01, b2StateSystem, sentenceOfCode_encode, he, Option.map_some,
        Option.getD_some]
      rfl
  genuine := by
    intro m c hc
    simp only [witnessIndex, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp

/-! ## K1 and K2 at B2 -/

/-- **K1 at B2**: over `paperDP 𝗜𝚺₁`, `halfRound`, the four-table grid: under
`PCPσ halfFamily (stateSentence …) fixedSystem01 P ∧ E5σ …`, for every pinned coordinate `c` and
cell `r ∈ {0, 1}`, `P n (cellSentence 𝗜𝚺₁ halfRound _ (n+1) c r) = cellMass …`.
Source: mandate § K1 (instantiated at `𝗜𝚺₁`, `halfRound`, `fixedSystem`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem forced_marginal_B2 (P : History)
    (hcoh : PCPσ halfFamily (stateSentence 𝗜𝚺₁ halfRound halfRound_computable) fixedSystem01 P)
    (hE5 : E5σ (stateSentence 𝗜𝚺₁ halfRound halfRound_computable) fixedSystem01 P) (n : ℕ)
    {c : ℕ} (hc : c ∈ pinned halfFamily witnessIndex n) {r : ℕ} (hr : r ∈ ({0, 1} : Finset ℕ)) :
    P n (cellSentence 𝗜𝚺₁ halfRound halfRound_computable (n + 1) c r) =
      cellMass (stateSentence 𝗜𝚺₁ halfRound halfRound_computable) fixedSystem01 P n c r :=
  forced_marginal halfFamily witnessIndex fixedSystem01 P fixedSystem01_tabular hcoh hE5 n hc hr

/-- `⊤ ∈ Sminus n m` from day `1` (no atoms).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma verum_mem_Sminus {n : ℕ} (hn : 1 ≤ n) (m : ℕ) : (⊤ : Sentence) ∈ Sminus n m := by
  rw [mem_Sminus]
  exact ⟨mem_smallSet.1 (top_mem_smallSet hn), fun a ha => by simp at ha⟩

/-- A pinned day for the family of record is `≥ 1` (a quotation atom has size `≥ 3`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma one_le_of_mem_pinned_B2 {n c : ℕ} (h : c ∈ pinned halfFamily witnessIndex n) : 1 ≤ n := by
  rw [mem_pinned] at h
  have h0 := h.2 0 (by simp [halfFamily, b2Family])
  unfold SmallOn at h0
  have h3 : 3 ≤ tokenSize (halfFamily.cellLit (n + 1) c 0) := three_le_tokenSize_atom _
  by_contra hn
  rw [not_le] at hn
  interval_cases n
  have : sizeBound 0 = 2 := by norm_num [sizeBound]
  omega

/-- **The scope condition of `determination` holds on `[⌜⊥⌝, ⌜⊤⌝]`**: `⊥` is small and in every
`Sminus`; `⊤` is small and in `Sminus (n+1) (n+1)` from day `1`, and a pinned day is `≥ 1`.
Source: mandate § K2 (the scope clauses)
Kind: L
Fidelity: exact -/
theorem scope_witnessIndex : ∀ n, ∀ c ∈ pinned halfFamily witnessIndex n,
    sentenceOfCode c ∈ smallSet n ∧ sentenceOfCode c ∈ Sminus (n + 1) (n + 1) := by
  intro n c hc
  have hn := one_le_of_mem_pinned_B2 hc
  have hc' := (mem_pinned.1 hc).1
  simp only [witnessIndex, List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with rfl | rfl
  · rw [sentenceOfCode_encode]; exact ⟨falsum_mem_smallSet n, falsum_mem_Sminus _ _⟩
  · rw [sentenceOfCode_encode]; exact ⟨top_mem_smallSet hn, verum_mem_Sminus (by omega) _⟩

/-- **K2 at B2 — the determination theorem over `paperDP 𝗜𝚺₁`**: a linked BLI
(`PCPσ ∧ E5σ ∧ E1x Q P ∧ E2xσIdx`) over the four-table grid forces `D_NNUcell halfFamily
witnessIndex Q` — exact no-net-update of the base on `⊥` and `⊤` from the day they are pinned.
Source: [[bli-program]] §3.6(ii); mandate § K2 ("instantiated at B2 over `paperDP 𝗜𝚺₁`")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem determination_B2 (Q P : History)
    (hcoh : PCPσ halfFamily (stateSentence 𝗜𝚺₁ halfRound halfRound_computable) fixedSystem01 P)
    (hE5 : E5σ (stateSentence 𝗜𝚺₁ halfRound halfRound_computable) fixedSystem01 P)
    (hE1 : E1x Q P)
    (hE2 : E2xσIdx (stateSentence 𝗜𝚺₁ halfRound halfRound_computable) witnessIndex fixedSystem01 P) :
    D_NNUcell halfFamily witnessIndex Q :=
  determination halfFamily witnessIndex fixedSystem01 Q P fixedSystem01_tabular hcoh hE5 hE1 hE2
    scope_witnessIndex

/-! ## The pinned set is eventually non-empty -/

/-- `Nat.pair` of two numbers below `4^i` is below `4^(2i)`.
Source: none: infrastructure (Mathlib `Nat.pair_lt_max_add_one_sq`)
Kind: L
Fidelity: n/a -/
lemma pair_lt_four_pow {x y i : ℕ} (hx : x < 4 ^ i) (hy : y < 4 ^ i) :
    Nat.pair x y < 4 ^ (2 * i) := by
  have h := Nat.pair_lt_max_add_one_sq x y
  have hm : max x y + 1 ≤ 4 ^ i := by
    rcases le_total x y with hxy | hxy
    · rw [max_eq_right hxy]; omega
    · rw [max_eq_left hxy]; omega
  calc Nat.pair x y < (max x y + 1) ^ 2 := h
    _ ≤ (4 ^ i) ^ 2 := Nat.pow_le_pow_left hm 2
    _ = 4 ^ (2 * i) := by rw [← pow_mul, mul_comm]

/-- Monotonicity of `· < 4 ^ ·` in the exponent.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lt_four_pow_mono {x i j : ℕ} (h : x < 4 ^ i) (hij : i ≤ j) : x < 4 ^ j :=
  lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hij)

/-- Every number is below `4^(its base-4 length)`, hence below `4^K` for any `K ≥` that length.
Source: none: infrastructure (`lt_pow_length_natDigits4`)
Kind: L
Fidelity: n/a -/
lemma lt_four_pow_of_le_length {x K : ℕ} (h : (natDigits4 x).length ≤ K) : x < 4 ^ K :=
  lt_four_pow_mono (lt_pow_length_natDigits4 x) h

/-- **The size budget constant of the cell quote code**: the base-4 lengths of the two schema
codes and of the quote program's code, plus `2`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def K₁ : ℕ :=
  (natDigits4 (Encodable.encode universalQuotePos)).length +
    (natDigits4 (Encodable.encode universalQuoteNeg)).length +
    (natDigits4 (cellQuote 𝗜𝚺₁ halfRound halfRound_computable).code).length + 2

/-- **The cell literal's atom index is bounded by `4^(64 (n + 1 + K₁))`** for a coordinate code
and a cell index below `4^K₁` (both hold for `⌜⊥⌝ = 1`, `⌜⊤⌝ = 12`, `r ∈ {0, 1}`).
Source: mandate § K1 ("the code is `Nat.pair`-polynomial in `n+1`, `⌜⊥⌝`, `r` and the fixed
`(marketQuoteCode T).code`")
Kind: L
Fidelity: n/a -/
lemma cellCode_lt (n c r : ℕ) (hc : c < 4 ^ K₁) (hr : r < 4 ^ K₁) :
    quotationClaimCode universalQuotePos universalQuoteNeg
      (Nat.pair (cellQuote 𝗜𝚺₁ halfRound halfRound_computable).code (Nat.pair (n + 1) (Nat.pair c r)))
      < 4 ^ (64 * (n + 1 + K₁)) := by
  set i := n + 1 + K₁ with hi
  have hK : K₁ ≤ i := by omega
  have hpos : Encodable.encode universalQuotePos < 4 ^ i :=
    lt_four_pow_of_le_length (by unfold K₁ at hi; omega)
  have hneg : Encodable.encode universalQuoteNeg < 4 ^ i :=
    lt_four_pow_of_le_length (by unfold K₁ at hi; omega)
  have hcode : (cellQuote 𝗜𝚺₁ halfRound halfRound_computable).code < 4 ^ i :=
    lt_four_pow_of_le_length (by unfold K₁ at hi; omega)
  have hn : n + 1 < 4 ^ i := by
    calc n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
      _ ≤ 4 ^ (n + 1) := Nat.pow_le_pow_left (by norm_num) _
      _ ≤ 4 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
  have htwo : 2 < 4 ^ i := by
    calc 2 < 4 ^ 1 := by norm_num
      _ ≤ 4 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hc' : c < 4 ^ i := lt_four_pow_mono hc hK
  have hr' : r < 4 ^ i := lt_four_pow_mono hr hK
  have h1 : Nat.pair c r < 4 ^ (2 * i) := pair_lt_four_pow hc' hr'
  have h2 : Nat.pair (n + 1) (Nat.pair c r) < 4 ^ (4 * i) := by
    have := pair_lt_four_pow (lt_four_pow_mono hn (by omega : i ≤ 2 * i)) h1
    rwa [show 2 * (2 * i) = 4 * i by ring] at this
  have h3 : Nat.pair (cellQuote 𝗜𝚺₁ halfRound halfRound_computable).code
      (Nat.pair (n + 1) (Nat.pair c r)) < 4 ^ (8 * i) := by
    have := pair_lt_four_pow (lt_four_pow_mono hcode (by omega : i ≤ 4 * i)) h2
    rwa [show 2 * (4 * i) = 8 * i by ring] at this
  have h4 : Nat.pair (Encodable.encode universalQuoteNeg)
      (Nat.pair (cellQuote 𝗜𝚺₁ halfRound halfRound_computable).code
        (Nat.pair (n + 1) (Nat.pair c r))) < 4 ^ (16 * i) := by
    have := pair_lt_four_pow (lt_four_pow_mono hneg (by omega : i ≤ 8 * i)) h3
    rwa [show 2 * (8 * i) = 16 * i by ring] at this
  have h5 : Nat.pair (Encodable.encode universalQuotePos)
      (Nat.pair (Encodable.encode universalQuoteNeg)
        (Nat.pair (cellQuote 𝗜𝚺₁ halfRound halfRound_computable).code
          (Nat.pair (n + 1) (Nat.pair c r)))) < 4 ^ (32 * i) := by
    have := pair_lt_four_pow (lt_four_pow_mono hpos (by omega : i ≤ 16 * i)) h4
    rwa [show 2 * (16 * i) = 32 * i by ring] at this
  unfold quotationClaimCode
  have := pair_lt_four_pow (lt_four_pow_mono htwo (by omega : i ≤ 32 * i)) h5
  rwa [show 2 * (32 * i) = 64 * i by ring] at this

/-- **An atom family with `Nat.pair`-polynomial indices is eventually day-small**: if
`a n < 4^(64 (n + 1 + K))`, then `atom (a n)` is small on day `n` for all `n ≥ K + 10`
(`tokenSize (atom a) = log₄`-length of `a + 5`, plus one, against `sizeBound n = 2^(2^n)`).
Source: mandate § K1 ("`∃ N` is what is provable"); `bli-found` `tokenSize_atom`
Kind: L
Fidelity: n/a -/
lemma smallOn_atom_of_lt_pow (a : ℕ → ℕ) (K : ℕ) (ha : ∀ n, a n < 4 ^ (64 * (n + 1 + K))) :
    ∀ n ≥ K + 10, SmallOn n (Formula.atom (a n)) := by
  intro n hn
  unfold SmallOn
  rw [tokenSize_atom]
  have h0 := ha n
  set m := n + 1 + K with hm
  have h1 : a n + 5 < 4 ^ (64 * m + 2) := by
    have hy : 1 ≤ 4 ^ (64 * m) := Nat.one_le_pow _ _ (by norm_num)
    rw [pow_add]
    omega
  have h2 : (natDigits4 (a n + 5)).length ≤ 64 * m + 2 := length_natDigits4_le_of_lt_pow h1
  have h3 : m < 2 ^ m := Nat.lt_two_pow_self
  have h4 : 64 * m + 3 ≤ 2 ^ (m + 7) := by
    rw [pow_add]
    have : (2 : ℕ) ^ 7 = 128 := by norm_num
    rw [this]
    omega
  have h5 : m + 7 ≤ 2 ^ n := by
    have hn1 : 1 ≤ n := by omega
    have h6 : n - 1 < 2 ^ (n - 1) := Nat.lt_two_pow_self
    have h7 : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have h6 : 2 ^ (m + 7) ≤ 2 ^ (2 ^ n) := Nat.pow_le_pow_right (by norm_num) h5
  unfold sizeBound
  omega

/-- `⌜⊥⌝ = 1` and `⌜⊤⌝ = 12` are below `4^K₁`, as are the cell indices `0`, `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma small_codes_lt :
    Encodable.encode (⊥ : Sentence) < 4 ^ K₁ ∧ Encodable.encode (⊤ : Sentence) < 4 ^ K₁ ∧
      (0 : ℕ) < 4 ^ K₁ ∧ (1 : ℕ) < 4 ^ K₁ := by
  have h16 : 16 ≤ 4 ^ K₁ := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ K₁ := Nat.pow_le_pow_right (by norm_num) (by unfold K₁; omega)
  have hb : Encodable.encode (⊥ : Sentence) = 1 := by decide
  have ht : Encodable.encode (⊤ : Sentence) = 12 := by decide
  omega

/-- **The pinned set is eventually non-empty — both coordinates of `[⌜⊥⌝, ⌜⊤⌝]` are pinned
from day `K₁ + 10` on**: every day-`(n+1)` cell literal of `⊥` and of `⊤` is small on day `n`.
Source: mandate § K1 ("Pinned set non-empty: prove `∃ N, ∀ n ≥ N, ⌜⊥⌝ ∈ pinned …` (and `⌜⊤⌝`)")
Kind: N+
Fidelity: exact (`∃ N`, as the mandate says is what is provable)
Hyps: (a) -/
theorem exists_pinned_from : ∃ N, ∀ n ≥ N,
    Encodable.encode (⊥ : Sentence) ∈ pinned halfFamily witnessIndex n ∧
      Encodable.encode (⊤ : Sentence) ∈ pinned halfFamily witnessIndex n := by
  obtain ⟨hb, ht, h0, h1⟩ := small_codes_lt
  refine ⟨K₁ + 10, fun n hn => ?_⟩
  have key : ∀ c, c < 4 ^ K₁ → ∀ r ∈ ({0, 1} : Finset ℕ),
      SmallOn n (halfFamily.cellLit (n + 1) c r) := by
    intro c hc r hr
    have hr' : r < 4 ^ K₁ := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl <;> assumption
    exact smallOn_atom_of_lt_pow
      (fun n => quotationClaimCode universalQuotePos universalQuoteNeg
        (Nat.pair (cellQuote 𝗜𝚺₁ halfRound halfRound_computable).code
          (Nat.pair (n + 1) (Nat.pair c r))))
      K₁ (fun n => cellCode_lt n c r hc hr') n hn
  constructor
  · rw [mem_pinned]; exact ⟨by simp [witnessIndex], fun r hr => key _ hb r hr⟩
  · rw [mem_pinned]; exact ⟨by simp [witnessIndex], fun r hr => key _ ht r hr⟩

/-! ## Two refutations about faith over list tables -/

/-- **Faith over a list-table system is unsatisfiable under coherence once the scope contains
an unlisted tautology**: if `ψ` holds in every world, lies in `Sminus (n+1) (n+1)`, and every
day-`(n+1)` candidate values it at `0`, then `E2xσ` fails for any `P` that is a partition-respecting
mixture at day `n` on an algebra containing `ψ ⋏ σ_q` and has partition mass one.
Source: this run (findings F-A1); bli-found F-2/F-12 (the junk value `0` off the index)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem e2xσ_unsat_of_unlisted_tautology {DP : DeductiveProcess} (C : CellFamily DP)
    (σ : ℕ → ℕ → Sentence) (S : StateSystem) (P : History) (n : ℕ) (D : Finset Sentence)
    (A : Finset ℕ) (hcoh : CoherentOnCell C D (n + 1) A (P n))
    (hAstate : ∀ q ∈ S.states (n + 1), sentenceAtomCodes (σ (n + 1) q) ⊆ A)
    (hmass : ∑ q ∈ S.states (n + 1), P n (σ (n + 1) q) = 1)
    (ψ : Sentence) (htaut : ∀ v : PCWorld, v.Holds ψ) (hψA : sentenceAtomCodes ψ ⊆ A)
    (hψS : ψ ∈ Sminus (n + 1) (n + 1)) (hval : ∀ q ∈ S.states (n + 1), S.val (n + 1) q ψ = 0) :
    ¬ E2xσ σ S P := by
  intro hE2
  obtain ⟨k, W, w, -, hw, hsum, hrep⟩ := hcoh
  -- some candidate has positive mass
  have hpos : ∃ q ∈ S.states (n + 1), 0 < P n (σ (n + 1) q) := by
    by_contra hall
    have : ∑ q ∈ S.states (n + 1), P n (σ (n + 1) q) ≤ 0 :=
      Finset.sum_nonpos fun q hq => not_lt.1 (fun h => hall ⟨q, hq, h⟩)
    linarith
  obtain ⟨q, hq, hqpos⟩ := hpos
  have h1 : P n (ψ ⋏ σ (n + 1) q) = P n (σ (n + 1) q) := by
    rw [hrep _ (by rw [sentenceAtomCodes_and]; exact Finset.union_subset hψA (hAstate q hq)),
      hrep _ (hAstate q hq)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [payout_and]
    unfold PCWorld.payout
    rw [if_pos (htaut (W i))]; ring
  have h2 := hE2 n (n + 1) (Nat.lt_succ_self n) q hq ψ hψS
  rw [hval q hq, zero_mul] at h2
  linarith

/-- `⊤ ⋏ ⊤` holds in every world, lies in `Sminus m m` from `m = 2` (`tokenSize = 10 ≤ sizeBound 2 = 16`), and is unlisted by every
fixed table (value `0` in `fixedSystem01`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma verum_and_verum_facts {m : ℕ} (hm : 2 ≤ m) :
    (∀ v : PCWorld, v.Holds ((⊤ : Sentence) ⋏ ⊤)) ∧ ((⊤ : Sentence) ⋏ ⊤) ∈ Sminus m m ∧
      ∀ q ∈ fixedStates m, fixedSystem01.val m q ((⊤ : Sentence) ⋏ ⊤) = 0 := by
  refine ⟨fun v => (PCWorld.holds_and v _ _).2 ⟨PCWorld.holds_top v, PCWorld.holds_top v⟩, ?_, ?_⟩
  · rw [mem_Sminus]
    refine ⟨?_, fun a ha => by
      rw [sentenceAtomCodes_and, sentenceAtomCodes_verum, Finset.union_empty] at ha
      exact absurd ha (by simp)⟩
    unfold SmallOn
    rw [tokenSize_and, tokenSize_verum]
    have : 16 ≤ sizeBound m := by
      calc 16 = sizeBound 2 := by norm_num [sizeBound]
        _ ≤ sizeBound m := sizeBound_mono hm
    omega
  · intro q hq
    simp only [fixedStates, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl <;>
    · simp only [fixedSystem01, b2StateSystem]
      rw [tableOfCode_encode]
      simp [tbl, entryOf]

/-- **`bli-found`'s full faith `E2xσ` is unsatisfiable over the four-table B2 system** by any
coherent `P` with partition mass one, from day `n = 1` (so `m = n+1 ≥ 2`): the unlisted
tautology `⊤ ⋏ ⊤` is in the scope with the junk value `0`.
Source: this run (findings F-A1)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem fixedSystem01_e2xσ_unsat (P : History) {n : ℕ} (hn : 1 ≤ n)
    (hcoh : PCPσ halfFamily (stateSentence 𝗜𝚺₁ halfRound halfRound_computable) fixedSystem01 P)
    (hE5 : E5σ (stateSentence 𝗜𝚺₁ halfRound halfRound_computable) fixedSystem01 P) :
    ¬ E2xσ (stateSentence 𝗜𝚺₁ halfRound halfRound_computable) fixedSystem01 P := by
  obtain ⟨htaut, hS, hval⟩ := verum_and_verum_facts (m := n + 1) (by omega)
  exact e2xσ_unsat_of_unlisted_tautology halfFamily _ fixedSystem01 P n (DP := paperDP 𝗜𝚺₁)
    ((paperDP 𝗜𝚺₁).D n) _ (hcoh n)
    (fun _ hq => (atoms_subset_stateAtomsσ hq).trans Finset.subset_union_right) (hE5 n).1
    _ htaut (by simp) hS hval

/-- **`witnessRep` cannot carry faith even on the index**: with `bli-found`'s representatives
`(1/4, 3/4)`, faith at the listed coordinate `⊥` (`∈ Sminus m m` always) demands
`P n (⊥ ⋏ σ_q) = val q ⊥ · P n σ_q` with `val q ⊥ ∈ {1/4, 3/4}`, while coherence gives `0`; so
every charged state dies, contradicting partition mass one. This is why `fixedSystem01` uses the
endpoint representatives `rep01`.
Source: this run (findings F-A2); mandate § K4c (whose "faith at `⊥`/`⊤` is `0`/`1`" presumes endpoint representatives)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem witnessRep_faith_unsat (P : History) (n : ℕ)
    (hcoh : PCPσ halfFamily (stateSentence 𝗜𝚺₁ halfRound halfRound_computable) fixedSystem P)
    (hE5 : E5σ (stateSentence 𝗜𝚺₁ halfRound halfRound_computable) fixedSystem P) :
    ¬ E2xσIdx (stateSentence 𝗜𝚺₁ halfRound halfRound_computable) witnessIndex fixedSystem P := by
  intro hE2
  obtain ⟨k, W, w, -, hw, hsum, hrep⟩ := hcoh n
  have hpos : ∃ q ∈ fixedSystem.states (n + 1), 0 < P n (stateSentence 𝗜𝚺₁ halfRound halfRound_computable (n + 1) q) := by
    by_contra hall
    have : ∑ q ∈ fixedSystem.states (n + 1),
        P n (stateSentence 𝗜𝚺₁ halfRound halfRound_computable (n + 1) q) ≤ 0 :=
      Finset.sum_nonpos fun q hq => not_lt.1 (fun h => hall ⟨q, hq, h⟩)
    linarith [(hE5 n).1]
  obtain ⟨q, hq, hqpos⟩ := hpos
  have hAq : sentenceAtomCodes (stateSentence 𝗜𝚺₁ halfRound halfRound_computable (n + 1) q) ⊆
      pcpAtomsσ (stateSentence 𝗜𝚺₁ halfRound halfRound_computable) fixedSystem n :=
    (atoms_subset_stateAtomsσ hq).trans Finset.subset_union_right
  have h1 : P n ((⊥ : Sentence) ⋏ stateSentence 𝗜𝚺₁ halfRound halfRound_computable (n + 1) q) = 0 := by
    rw [hrep _ (by rw [sentenceAtomCodes_and]; exact Finset.union_subset (by simp) hAq)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [payout_and]
    unfold PCWorld.payout
    rw [if_neg (show ¬ (W i).Holds ⊥ from fun h => h)]; ring
  have h2 := hE2 n (n + 1) (Nat.lt_succ_self n) q hq (Encodable.encode (⊥ : Sentence))
    (by simp [witnessIndex]) (by rw [sentenceOfCode_encode]; exact falsum_mem_Sminus _ _)
  rw [sentenceOfCode_encode, h1] at h2
  -- the value of `⊥` in a fixed table is `1/4` or `3/4`
  have hval : fixedSystem.val (n + 1) q ⊥ = 1 / 4 ∨ fixedSystem.val (n + 1) q ⊥ = 3 / 4 := by
    simp only [fixedSystem, b2StateSystem, fixedStates, Finset.mem_insert,
      Finset.mem_singleton] at hq ⊢
    rcases hq with rfl | rfl | rfl | rfl <;>
    · rw [tableOfCode_encode, (entryOf_tbl _ _).1]
      simp [witnessRep]
  rcases hval with hv | hv <;> rw [hv] at h2 <;> linarith

end B2

end Cleanroom.Bli.BliLinkage.AttemptA
