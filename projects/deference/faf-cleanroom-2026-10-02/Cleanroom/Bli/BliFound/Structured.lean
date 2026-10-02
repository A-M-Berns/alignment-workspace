import Cleanroom.Bli.BliFound.Size
import LogicalInduction.Framework.Emission.RpnSentence

/-!
# `bli-found` · Structured: the structured-escape size bound

**The claim.** A sentence read by FAF's structured paper-prime escape
(`parseStructuredPaperPrime`, `Framework/Criterion.lean:1824–1935`) from a block of `L` consumed
tokens has `tokenSize ≤ 2 ^ (C · L) + C` for a fixed `C` (`tokenSize_le_of_structured`, with
`C = 10`). This is the one escape bound the bridge lemma (`Bridge.lean`) needs beyond the Gödel
escape; the previous formalizer stated it OPEN because the numeric De Morgan involution
`negFormulaCode` (tokens `20`–`22`) resists a digit-count invariant: additive and multiplicative
slop compounds across nesting levels.

**The route (structural, not numeric).** Every formula code the parser emits is a *tree* whose
leaves are codes `Nat.pair a c + 1` with `a ≤ 3` (`rel`/`nrel`/`verum`/`falsum`) and whose
internal nodes are `Nat.pair a (Nat.pair x y) + 1` with `a ∈ {4, 5}` (`and`/`or`) or
`Nat.pair a x + 1` with `a ∈ {6, 7}` (`all`/`exs`). The predicate `FTree k D n` ("`n` is such a
tree of depth `≤ D` whose leaves are `< 4 ^ k`") is:

* **closed under `negFormulaCode` at the same depth**, with the leaf bound growing by two digits
  (`FTree.neg`): the involution swaps tags and recurses into subtrees, so the tree shape is
  preserved exactly, whatever the numeric values do;
* **numerically bounded by shape alone** (`FTree.lt_pow`): `n < 4 ^ (4 ^ D · k)`, because each
  node is at most two `Nat.pair`s of its children and a `Nat.pair` at most doubles a digit count.

So the number of nested negations is irrelevant: a parse with fuel `f` yields
`FTree (32 · 64 ^ f) (2 f) code` (`parseStructured_bounds`), hence `code < 4 ^ (2 ^ (10 f + 5))`,
hence the tag-`5` atom has at most `2 ^ (10 f + 7) + 2` digits, and the escape consumes at least
`f + 2` tokens.

Sources: mandate D3 (`tokenSize_le_of_structured`), findings F-4b; FAF's codec at
`Framework/Criterion.lean:1758–1935`.
-/

namespace Cleanroom.Bli.BliFound

open LogicalInduction LO.Propositional

/-! ## Digit arithmetic for `Nat.pair` -/

/-- A pair of numbers below `4 ^ k` is below `4 ^ (2 k)`: pairing at most doubles the digit count.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pair_lt_pow_of_lt {a b k : ℕ} (ha : a < 4 ^ k) (hb : b < 4 ^ k) :
    Nat.pair a b < 4 ^ (2 * k) := by
  have h := Nat.pair_lt_max_add_one_sq a b
  have hmax : max a b + 1 ≤ 4 ^ k := by
    rcases le_total a b with hab | hab
    · rw [max_eq_right hab]; omega
    · rw [max_eq_left hab]; omega
  calc Nat.pair a b < (max a b + 1) ^ 2 := h
    _ ≤ (4 ^ k) ^ 2 := Nat.pow_le_pow_left hmax 2
    _ = 4 ^ (2 * k) := by ring

/-- The successor of a pair of numbers below `4 ^ k` is below `4 ^ (2 k + 1)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pair_succ_lt_pow_of_lt {a b k : ℕ} (ha : a < 4 ^ k) (hb : b < 4 ^ k) :
    Nat.pair a b + 1 < 4 ^ (2 * k + 1) := by
  have h := pair_lt_pow_of_lt ha hb
  rw [pow_succ]
  have : 1 ≤ 4 ^ (2 * k) := Nat.one_le_pow _ _ (by norm_num)
  omega

/-- A small tag (`≤ 7`) paired with a number below `4 ^ k` (`k ≥ 2`) stays, with its successor,
below `4 ^ (2 k)` — no extra digit for the tag.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pair_small_succ_lt_pow {a b k : ℕ} (ha : a ≤ 7) (hb : b < 4 ^ k) (hk : 2 ≤ k) :
    Nat.pair a b + 1 < 4 ^ (2 * k) := by
  have h16 : 16 ≤ 4 ^ k := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rw [show 4 ^ (2 * k) = 4 ^ k * 4 ^ k by rw [two_mul, pow_add]]
  have hsq : 256 ≤ 4 ^ k * 4 ^ k := by
    calc 256 = 16 * 16 := by norm_num
      _ ≤ 4 ^ k * 4 ^ k := Nat.mul_le_mul h16 h16
  unfold Nat.pair
  split_ifs with hab
  · rcases Nat.lt_or_ge b 4 with hb4 | hb4
    · have : b * b ≤ 3 * 3 := Nat.mul_le_mul (by omega) (by omega)
      omega
    · have hb1 : b + 1 ≤ 4 ^ k := hb
      have := Nat.mul_le_mul hb1 hb1
      nlinarith
  · have hba : b ≤ a := not_lt.mp hab
    have : a * a ≤ 7 * 7 := Nat.mul_le_mul ha ha
    omega

/-- `Nat.pair 1 c ≤ Nat.pair 0 c + 2` (the `rel ↔ nrel` tag swap costs at most two).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pair_one_le_pair_zero_add_two (c : ℕ) : Nat.pair 1 c ≤ Nat.pair 0 c + 2 := by
  rcases Nat.lt_or_ge 1 c with h | h
  · have h0 : 0 < c := by omega
    simp only [Nat.pair, if_pos h, if_pos h0]
    omega
  · interval_cases c <;> decide

/-! ## The formula-code tree predicate -/

/-- **Formula-code trees.** `FTree k D n`: the number `n` is a Foundation formula code built as a
tree of depth `≤ D` from leaves `Nat.pair a c + 1` with `a ≤ 3` (`rel`/`nrel`/`verum`/`falsum`),
all `< 4 ^ k`, by the binary constructors `Nat.pair a (Nat.pair x y) + 1`, `a ∈ {4, 5}`
(`and`/`or`) and the unary constructors `Nat.pair a x + 1`, `a ∈ {6, 7}` (`all`/`exs`). This is
the shape every code of `parseStructuredArithmeticFormula` has, and the shape `negFormulaCode`
preserves.
Source: none: infrastructure (FAF's codec, `Framework/Criterion.lean:1774–1810`)
Kind: D
Fidelity: n/a -/
inductive FTree : ℕ → ℕ → ℕ → Prop
  | leaf {k D a c : ℕ} (ha : a ≤ 3) (hlt : Nat.pair a c + 1 < 4 ^ k) :
      FTree k D (Nat.pair a c + 1)
  | bin {k D a x y : ℕ} (ha : a = 4 ∨ a = 5) (hx : FTree k D x) (hy : FTree k D y) :
      FTree k (D + 1) (Nat.pair a (Nat.pair x y) + 1)
  | un {k D a x : ℕ} (ha : a = 6 ∨ a = 7) (hx : FTree k D x) :
      FTree k (D + 1) (Nat.pair a x + 1)

/-- `FTree` is monotone in the leaf digit bound and the depth.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma FTree.mono {k D n : ℕ} (h : FTree k D n) {k' D' : ℕ} (hk : k ≤ k') (hD : D ≤ D') :
    FTree k' D' n := by
  induction h generalizing k' D' with
  | leaf ha hlt =>
      exact FTree.leaf ha (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hk))
  | bin ha _ _ ihx ihy =>
      obtain ⟨D'', rfl⟩ : ∃ D'', D' = D'' + 1 := ⟨D' - 1, by omega⟩
      exact FTree.bin ha (ihx hk (by omega)) (ihy hk (by omega))
  | un ha _ ihx =>
      obtain ⟨D'', rfl⟩ : ∃ D'', D' = D'' + 1 := ⟨D' - 1, by omega⟩
      exact FTree.un ha (ihx hk (by omega))

/-- **The tree bound.** A formula-code tree of depth `D` with leaves below `4 ^ k` (`k ≥ 2`) is
below `4 ^ (4 ^ D · k)`: every node is at most two `Nat.pair`s of its children.
Source: none: infrastructure
Kind: P
Fidelity: n/a -/
lemma FTree.lt_pow {k D n : ℕ} (h : FTree k D n) (hk : 2 ≤ k) : n < 4 ^ (4 ^ D * k) := by
  induction h with
  | @leaf D a c ha hlt =>
      have hpos : 1 ≤ 4 ^ D := Nat.one_le_pow _ _ (by norm_num)
      exact lt_of_lt_of_le hlt
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left k hpos))
  | @bin D a x y ha hx hy ihx ihy =>
      have hpos : 1 ≤ 4 ^ D := Nat.one_le_pow _ _ (by norm_num)
      have hK : 2 ≤ 4 ^ D * k := le_trans hk (Nat.le_mul_of_pos_left k hpos)
      have h1 : Nat.pair x y < 4 ^ (2 * (4 ^ D * k)) := pair_lt_pow_of_lt ihx ihy
      have ha7 : a ≤ 7 := by rcases ha with rfl | rfl <;> norm_num
      have h2 : Nat.pair a (Nat.pair x y) + 1 < 4 ^ (2 * (2 * (4 ^ D * k))) :=
        pair_small_succ_lt_pow ha7 h1 (by omega)
      have heq : 2 * (2 * (4 ^ D * k)) = 4 ^ (D + 1) * k := by rw [pow_succ]; ring
      rw [← heq]; exact h2
  | @un D a x ha hx ihx =>
      have hpos : 1 ≤ 4 ^ D := Nat.one_le_pow _ _ (by norm_num)
      have hK : 2 ≤ 4 ^ D * k := le_trans hk (Nat.le_mul_of_pos_left k hpos)
      have ha7 : a ≤ 7 := by rcases ha with rfl | rfl <;> norm_num
      have h2 : Nat.pair a x + 1 < 4 ^ (2 * (4 ^ D * k)) := pair_small_succ_lt_pow ha7 ihx hK
      have hle : 2 * (4 ^ D * k) ≤ 4 ^ (D + 1) * k := by
        calc 2 * (4 ^ D * k) = (2 * 4 ^ D) * k := by ring
          _ ≤ (4 ^ D * 4) * k := Nat.mul_le_mul_right k (by omega)
          _ = 4 ^ (D + 1) * k := by rw [pow_succ]
      exact lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by norm_num) hle)

/-! ## `negFormulaCode` on each constructor -/

/-- `negFormulaCode` on a `rel` code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma negFormulaCode_pair0 (c : ℕ) : negFormulaCode (Nat.pair 0 c + 1) = Nat.pair 1 c + 1 := by
  rw [negFormulaCode]; simp [Nat.unpair_pair]

/-- `negFormulaCode` on an `nrel` code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma negFormulaCode_pair1 (c : ℕ) : negFormulaCode (Nat.pair 1 c + 1) = Nat.pair 0 c + 1 := by
  rw [negFormulaCode]; simp [Nat.unpair_pair]

/-- `negFormulaCode` on a `verum` code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma negFormulaCode_pair2 (c : ℕ) : negFormulaCode (Nat.pair 2 c + 1) = Nat.pair 3 0 + 1 := by
  rw [negFormulaCode]; simp [Nat.unpair_pair]

/-- `negFormulaCode` on a `falsum` code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma negFormulaCode_pair3 (c : ℕ) : negFormulaCode (Nat.pair 3 c + 1) = Nat.pair 2 0 + 1 := by
  rw [negFormulaCode]; simp [Nat.unpair_pair]

/-- `negFormulaCode` on an `and` code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma negFormulaCode_pair4 (x y : ℕ) :
    negFormulaCode (Nat.pair 4 (Nat.pair x y) + 1) =
      Nat.pair 5 (Nat.pair (negFormulaCode x) (negFormulaCode y)) + 1 := by
  rw [negFormulaCode]; simp [Nat.unpair_pair]

/-- `negFormulaCode` on an `or` code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma negFormulaCode_pair5 (x y : ℕ) :
    negFormulaCode (Nat.pair 5 (Nat.pair x y) + 1) =
      Nat.pair 4 (Nat.pair (negFormulaCode x) (negFormulaCode y)) + 1 := by
  rw [negFormulaCode]; simp [Nat.unpair_pair]

/-- `negFormulaCode` on an `all` code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma negFormulaCode_pair6 (x : ℕ) :
    negFormulaCode (Nat.pair 6 x + 1) = Nat.pair 7 (negFormulaCode x) + 1 := by
  rw [negFormulaCode]; simp [Nat.unpair_pair]

/-- `negFormulaCode` on an `exs` code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma negFormulaCode_pair7 (x : ℕ) :
    negFormulaCode (Nat.pair 7 x + 1) = Nat.pair 6 (negFormulaCode x) + 1 := by
  rw [negFormulaCode]; simp [Nat.unpair_pair]

/-- **The De Morgan involution preserves tree shape.** `FTree k D n → FTree (k + 2) D
(negFormulaCode n)`: the depth is unchanged and the leaves grow by at most two digits (the
`rel ↔ nrel` swap adds at most `2`, `verum ↔ falsum` gives `13` or `7`). This is what makes the
numeric growth of `negFormulaCode` irrelevant to the size bound.
Source: none: infrastructure (findings F-4b, resolved)
Kind: P
Fidelity: n/a -/
lemma FTree.neg {k D n : ℕ} (h : FTree k D n) : FTree (k + 2) D (negFormulaCode n) := by
  induction h with
  | @leaf D a c ha hlt =>
      have h16 : 4 ^ (k + 2) = 4 ^ k * 16 := by rw [pow_add]; norm_num
      have hk1 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
      interval_cases a
      · rw [negFormulaCode_pair0]
        refine FTree.leaf (by norm_num) ?_
        have := pair_one_le_pair_zero_add_two c
        omega
      · rw [negFormulaCode_pair1]
        refine FTree.leaf (by norm_num) ?_
        have := (Nat.pair_lt_pair_left c (show 0 < 1 by norm_num)).le
        omega
      · rw [negFormulaCode_pair2]
        refine FTree.leaf (by norm_num) ?_
        have : Nat.pair 3 0 + 1 = 13 := by decide
        omega
      · rw [negFormulaCode_pair3]
        refine FTree.leaf (by norm_num) ?_
        have : Nat.pair 2 0 + 1 = 7 := by decide
        omega
  | @bin D a x y ha hx hy ihx ihy =>
      rcases ha with rfl | rfl
      · rw [negFormulaCode_pair4]
        exact FTree.bin (Or.inr rfl) ihx ihy
      · rw [negFormulaCode_pair5]
        exact FTree.bin (Or.inl rfl) ihx ihy
  | @un D a x ha hx ihx =>
      rcases ha with rfl | rfl
      · rw [negFormulaCode_pair6]
        exact FTree.un (Or.inr rfl) ihx
      · rw [negFormulaCode_pair7]
        exact FTree.un (Or.inl rfl) ihx

/-! ## The parser bounds -/

/-- **Digit budget at fuel `f`**: `32 · 64 ^ f`. Every term code the term parser emits with fuel
`f` is below `4 ^ termDigits f`, and every formula code the formula parser emits with fuel `f` is
an `FTree (termDigits f) (2 f)`. The factor `64` absorbs the five `Nat.pair`s of a binary
function or relation code (`32 T + 31 ≤ 64 T`) and the `+ 2` of a negation.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def termDigits (f : ℕ) : ℕ := 32 * 64 ^ f

/-- `termDigits_succ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma termDigits_succ (f : ℕ) : termDigits (f + 1) = 64 * termDigits f := by
  unfold termDigits; rw [pow_succ]; ring

/-- `32 ≤ termDigits f`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma thirtytwo_le_termDigits (f : ℕ) : 32 ≤ termDigits f := by
  unfold termDigits
  have : 1 ≤ 64 ^ f := Nat.one_le_pow _ _ (by norm_num)
  omega

/-- `2 ≤ termDigits f`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma two_le_termDigits (f : ℕ) : 2 ≤ termDigits f := le_trans (by norm_num) (thirtytwo_le_termDigits f)

/-- `f < 2 ^ f`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lt_two_pow' (f : ℕ) : f < 2 ^ f := by
  induction f with
  | zero => norm_num
  | succ f ih => rw [pow_succ]; omega

/-- A binary numeral of `f` tokens is below `4 ^ f`, and `2 f + 3 ≤ termDigits f`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma two_mul_add_three_le_termDigits (f : ℕ) : 2 * f + 3 ≤ termDigits f := by
  have h1 := lt_two_pow' f
  have h2 : 2 ^ f ≤ 64 ^ f := Nat.pow_le_pow_left (by norm_num) f
  unfold termDigits
  omega

/-- `n < 4 ^ k` is monotone in `k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lt_pow_mono {n k k' : ℕ} (h : n < 4 ^ k) (hk : k ≤ k') : n < 4 ^ k' :=
  lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hk)

/-- Strip the successor: `n + 1 < 4 ^ k → n < 4 ^ k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lt_pow_of_succ_lt {n k : ℕ} (h : n + 1 < 4 ^ k) : n < 4 ^ k := by omega

/-- A number below `64` is below `4 ^ termDigits f`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lt_pow_termDigits_of_lt_64 {c : ℕ} (f : ℕ) (hc : c < 64) : c < 4 ^ termDigits f :=
  lt_pow_mono (show c < 4 ^ 3 by norm_num; omega)
    (le_trans (by norm_num) (thirtytwo_le_termDigits f))

/-- The two-element argument-vector code of two codes below `4 ^ T` is below `4 ^ (4 T + 3)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma arithmeticVec2Code_lt {p q T : ℕ} (hp : p < 4 ^ T) (hq : q < 4 ^ T) :
    arithmeticVec2Code p q < 4 ^ (4 * T + 3) := by
  unfold arithmeticVec2Code
  have h0 : 0 < 4 ^ T := Nat.one_le_pow _ _ (by norm_num)
  have h1 : Nat.pair q 0 + 1 < 4 ^ (2 * T + 1) := pair_succ_lt_pow_of_lt hq h0
  have hp' : p < 4 ^ (2 * T + 1) := lt_pow_mono hp (by omega)
  have h2 := pair_succ_lt_pow_of_lt hp' h1
  exact lt_pow_mono h2 (by omega)

/-- A binary function-symbol term code over argument codes below `4 ^ T` is below
`4 ^ (32 T + 31)` (five `Nat.pair`s).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma arithmeticFuncCode_two_lt {s p q T : ℕ} (hs : s ≤ 1) (hp : p < 4 ^ T) (hq : q < 4 ^ T) :
    arithmeticFuncCode 2 s (arithmeticVec2Code p q) < 4 ^ (32 * T + 31) := by
  unfold arithmeticFuncCode
  have hv := arithmeticVec2Code_lt hp hq
  have hs' : s < 4 ^ (4 * T + 3) := lt_pow_mono (show s < 4 ^ 1 by omega) (by omega)
  have h1 := pair_succ_lt_pow_of_lt hs' hv
  have h1' : Nat.pair s (arithmeticVec2Code p q) < 4 ^ (8 * T + 7) :=
    lt_pow_mono (lt_pow_of_succ_lt h1) (by omega)
  have h2' : 2 < 4 ^ (8 * T + 7) := lt_pow_mono (show 2 < 4 ^ 1 by norm_num) (by omega)
  have h2 := pair_succ_lt_pow_of_lt h2' h1'
  have h2'' : Nat.pair 2 (Nat.pair s (arithmeticVec2Code p q)) < 4 ^ (16 * T + 15) :=
    lt_pow_mono (lt_pow_of_succ_lt h2) (by omega)
  have h3' : 2 < 4 ^ (16 * T + 15) := lt_pow_mono (show 2 < 4 ^ 1 by norm_num) (by omega)
  have h3 := pair_succ_lt_pow_of_lt h3' h2''
  exact lt_pow_mono h3 (by omega)

/-- A binary relation code over term codes below `4 ^ T` is an `FTree` leaf whenever the leaf
budget is at least `32 T + 31`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma FTree_arithmeticRelCode {b : Bool} {s p q T k D : ℕ} (hs : s ≤ 1) (hp : p < 4 ^ T)
    (hq : q < 4 ^ T) (hk : 32 * T + 31 ≤ k) : FTree k D (arithmeticRelCode b s p q) := by
  unfold arithmeticRelCode
  have hv := arithmeticVec2Code_lt hp hq
  have hs' : s < 4 ^ (4 * T + 3) := lt_pow_mono (show s < 4 ^ 1 by omega) (by omega)
  have h1 := pair_succ_lt_pow_of_lt hs' hv
  have h1' : Nat.pair s (arithmeticVec2Code p q) < 4 ^ (8 * T + 7) :=
    lt_pow_mono (lt_pow_of_succ_lt h1) (by omega)
  have h2' : 2 < 4 ^ (8 * T + 7) := lt_pow_mono (show 2 < 4 ^ 1 by norm_num) (by omega)
  have h2 := pair_succ_lt_pow_of_lt h2' h1'
  have h2'' : Nat.pair 2 (Nat.pair s (arithmeticVec2Code p q)) < 4 ^ (16 * T + 15) :=
    lt_pow_mono (lt_pow_of_succ_lt h2) (by omega)
  have hb' : (if b then 1 else 0) < 4 ^ (16 * T + 15) :=
    lt_pow_mono (show (if b then 1 else 0) < 4 ^ 1 by split_ifs <;> norm_num) (by omega)
  have h3 := pair_succ_lt_pow_of_lt hb' h2''
  exact FTree.leaf (by split_ifs <;> norm_num) (lt_pow_mono h3 (by omega))

/-- **The parser bounds.** With fuel `f`: a parsed numeral is `< 2 ^ f`; a parsed term code is
`< 4 ^ termDigits f`; a parsed formula code is an `FTree (termDigits f) (2 f)` — a tree of depth
`≤ 2 f` with leaves below `4 ^ termDigits f`. Simultaneous induction on the fuel over the three
mutually recursive parsers; the negation cases (tokens `20`–`22`) go through `FTree.neg`.
Source: none: infrastructure (FAF's codec, `Framework/Criterion.lean:1824–1894`)
Kind: P
Fidelity: n/a -/
theorem parseStructured_bounds : ∀ f : ℕ,
    (∀ (ts : List ℕ) (v : ℕ) (r : List ℕ), parseStructuredNat f ts = some (v, r) → v < 2 ^ f) ∧
    (∀ (ts : List ℕ) (c : ℕ) (r : List ℕ), parseStructuredArithmeticTerm f ts = some (c, r) →
        c < 4 ^ termDigits f) ∧
    (∀ (ts : List ℕ) (c : ℕ) (r : List ℕ), parseStructuredArithmeticFormula f ts = some (c, r) →
        FTree (termDigits f) (2 * f) c) := by
  intro f
  induction f with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro ts v r h; simp [parseStructuredNat] at h
      · intro ts c r h; simp [parseStructuredArithmeticTerm] at h
      · intro ts c r h; simp [parseStructuredArithmeticFormula] at h
  | succ f ih =>
      obtain ⟨ihN, ihT, ihF⟩ := ih
      have hT2 := two_le_termDigits f
      have hTsucc := termDigits_succ f
      have hT3 := two_mul_add_three_le_termDigits f
      refine ⟨?_, ?_, ?_⟩
      · -- numerals
        intro ts v r h
        rcases ts with _ | ⟨t, ts⟩
        · simp [parseStructuredNat] at h
        rw [parseStructuredNat] at h
        by_cases h0 : t = 0
        · rw [if_pos h0] at h
          obtain ⟨rfl, -⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
          exact Nat.one_le_pow _ _ (by norm_num)
        rw [if_neg h0] at h
        by_cases h1 : t = 1
        · rw [if_pos h1] at h
          rcases hp : parseStructuredNat f ts with _ | ⟨v', r'⟩ <;> simp [hp] at h
          obtain ⟨rfl, rfl⟩ := h
          have := ihN ts v' r' hp
          rw [pow_succ]; omega
        rw [if_neg h1] at h
        by_cases h2 : t = 2
        · rw [if_pos h2] at h
          rcases hp : parseStructuredNat f ts with _ | ⟨v', r'⟩ <;> simp [hp] at h
          obtain ⟨rfl, rfl⟩ := h
          have := ihN ts v' r' hp
          rw [pow_succ]; omega
        rw [if_neg h2] at h
        simp at h
      · -- terms
        intro ts c r h
        rcases ts with _ | ⟨t, ts⟩
        · simp [parseStructuredArithmeticTerm] at h
        rw [parseStructuredArithmeticTerm] at h
        by_cases h3 : t = 3
        · rw [if_pos h3] at h
          rcases hp : parseStructuredNat f ts with _ | ⟨v', r'⟩ <;> simp [hp] at h
          obtain ⟨rfl, rfl⟩ := h
          have hv := ihN ts v' r' hp
          have hv4 : v' < 4 ^ (f + 1) :=
            lt_of_lt_of_le hv (le_trans (Nat.pow_le_pow_left (by norm_num) f)
              (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ f)))
          have h0 : 0 < 4 ^ (f + 1) := Nat.one_le_pow _ _ (by norm_num)
          exact lt_pow_mono (pair_succ_lt_pow_of_lt h0 hv4) (by omega)
        rw [if_neg h3] at h
        by_cases h4 : t = 4
        · rw [if_pos h4] at h
          rcases hp : parseStructuredNat f ts with _ | ⟨v', r'⟩ <;> simp [hp] at h
          obtain ⟨rfl, rfl⟩ := h
          have hv := ihN ts v' r' hp
          have hv4 : v' < 4 ^ (f + 1) :=
            lt_of_lt_of_le hv (le_trans (Nat.pow_le_pow_left (by norm_num) f)
              (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ f)))
          have h1 : 1 < 4 ^ (f + 1) := lt_pow_mono (show 1 < 4 ^ 1 by norm_num) (by omega)
          exact lt_pow_mono (pair_succ_lt_pow_of_lt h1 hv4) (by omega)
        rw [if_neg h4] at h
        by_cases h5 : t = 5
        · rw [if_pos h5] at h
          obtain ⟨rfl, -⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
          exact lt_pow_termDigits_of_lt_64 _ (by decide)
        rw [if_neg h5] at h
        by_cases h6 : t = 6
        · rw [if_pos h6] at h
          obtain ⟨rfl, -⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
          exact lt_pow_termDigits_of_lt_64 _ (by decide)
        rw [if_neg h6] at h
        by_cases h78 : t = 7 ∨ t = 8
        · rw [if_pos h78] at h
          rcases hp : parseStructuredArithmeticTerm f ts with _ | ⟨p1, p2⟩ <;> simp [hp] at h
          rcases hq : parseStructuredArithmeticTerm f p2 with _ | ⟨q1, q2⟩ <;> simp [hq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hp' := ihT ts p1 p2 hp
          have hq' := ihT p2 q1 q2 hq
          have := arithmeticFuncCode_two_lt (s := if t = 7 then 0 else 1)
            (by split_ifs <;> norm_num) hp' hq'
          exact lt_pow_mono this (by omega)
        rw [if_neg h78] at h
        simp at h
      · -- formulas
        intro ts c r h
        rcases ts with _ | ⟨t, ts⟩
        · simp [parseStructuredArithmeticFormula] at h
        rw [parseStructuredArithmeticFormula] at h
        by_cases h9 : t = 9
        · rw [if_pos h9] at h
          obtain ⟨rfl, -⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
          exact FTree.leaf (by norm_num) (lt_pow_termDigits_of_lt_64 _ (by decide))
        rw [if_neg h9] at h
        by_cases h10 : t = 10
        · rw [if_pos h10] at h
          obtain ⟨rfl, -⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
          exact FTree.leaf (by norm_num) (lt_pow_termDigits_of_lt_64 _ (by decide))
        rw [if_neg h10] at h
        by_cases hrel : t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14
        · rw [if_pos hrel] at h
          rcases hp : parseStructuredArithmeticTerm f ts with _ | ⟨p1, p2⟩ <;> simp [hp] at h
          rcases hq : parseStructuredArithmeticTerm f p2 with _ | ⟨q1, q2⟩ <;> simp [hq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact FTree_arithmeticRelCode (s := if t = 11 ∨ t = 12 then 0 else 1)
            (by split_ifs <;> norm_num) (ihT ts p1 p2 hp)
            (ihT p2 q1 q2 hq) (by omega)
        rw [if_neg hrel] at h
        by_cases hbin : t = 15 ∨ t = 16
        · rw [if_pos hbin] at h
          rcases hp : parseStructuredArithmeticFormula f ts with _ | ⟨p1, p2⟩ <;> simp [hp] at h
          rcases hq : parseStructuredArithmeticFormula f p2 with _ | ⟨q1, q2⟩ <;> simp [hq] at h
          obtain ⟨rfl, rfl⟩ := h
          have := FTree.bin (a := if t = 15 then 4 else 5) (by split_ifs <;> simp)
            (ihF ts p1 p2 hp) (ihF p2 q1 q2 hq)
          exact this.mono (by omega) (by omega)
        rw [if_neg hbin] at h
        by_cases hquant : t = 17 ∨ t = 18
        · rw [if_pos hquant] at h
          rcases hp : parseStructuredArithmeticFormula f ts with _ | ⟨p1, p2⟩ <;> simp [hp] at h
          obtain ⟨rfl, rfl⟩ := h
          have := FTree.un (a := if t = 17 then 6 else 7) (by split_ifs <;> simp) (ihF ts p1 p2 hp)
          exact this.mono (by omega) (by omega)
        rw [if_neg hquant] at h
        by_cases h20 : t = 20
        · rw [if_pos h20] at h
          rcases hp : parseStructuredArithmeticFormula f ts with _ | ⟨p1, p2⟩ <;> simp [hp] at h
          obtain ⟨rfl, rfl⟩ := h
          exact (ihF ts p1 p2 hp).neg.mono (by omega) (by omega)
        rw [if_neg h20] at h
        by_cases h21 : t = 21
        · rw [if_pos h21] at h
          rcases hp : parseStructuredArithmeticFormula f ts with _ | ⟨p1, p2⟩ <;> simp [hp] at h
          rcases hq : parseStructuredArithmeticFormula f p2 with _ | ⟨q1, q2⟩ <;> simp [hq] at h
          obtain ⟨rfl, rfl⟩ := h
          have := FTree.bin (Or.inr rfl) (ihF ts p1 p2 hp).neg
            ((ihF p2 q1 q2 hq).mono (by omega) le_rfl)
          exact this.mono (by omega) (by omega)
        rw [if_neg h21] at h
        by_cases h22 : t = 22
        · rw [if_pos h22] at h
          rcases hp : parseStructuredArithmeticFormula f ts with _ | ⟨p1, p2⟩ <;> simp [hp] at h
          rcases hq : parseStructuredArithmeticFormula f p2 with _ | ⟨q1, q2⟩ <;> simp [hq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hp' := ihF ts p1 p2 hp
          have hq' := ihF p2 q1 q2 hq
          have hleft := FTree.bin (Or.inr rfl) hp'.neg (hq'.mono (by omega) le_rfl)
          have hright := FTree.bin (Or.inr rfl) hq'.neg (hp'.mono (by omega) le_rfl)
          have := FTree.bin (Or.inl rfl) hleft hright
          exact this.mono (by omega) (by omega)
        rw [if_neg h22] at h
        simp at h

/-! ## The escape bound -/

/-- `4 ^ (2 f) · termDigits f = 2 ^ (10 f + 5)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma four_pow_mul_termDigits (f : ℕ) : 4 ^ (2 * f) * termDigits f = 2 ^ (10 * f + 5) := by
  have h4 : (4 : ℕ) ^ (2 * f) = 2 ^ (4 * f) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
  have h64 : (64 : ℕ) ^ f = 2 ^ (6 * f) := by
    rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_mul]
  unfold termDigits
  rw [h4, h64]
  ring

/-- **The structured-escape size bound** (closes findings F-4b). A sentence read by the structured
paper-prime escape from a block of `L` consumed tokens has `tokenSize ≤ 2 ^ (10 L) + 10`: the
escape with payload length `f` consumes `2 f + 3 ≥ f + 2` tokens, its formula code is an
`FTree (32 · 64 ^ f) (2 f)` (`parseStructured_bounds`), hence below
`4 ^ (2 ^ (10 f + 5))` (`FTree.lt_pow`), and the tag-`5` atom's index
`Nat.pair 5 (Nat.pair polarity code)` then has at most `2 ^ (10 f + 7) + 1` base-4 digits.
Stated exactly as the bridge lemma consumes it (`∃ C`).
Source: mandate D3/T1 (`tokenSize_le_of_structured`); findings F-4b
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem tokenSize_le_of_structured :
    ∃ C : ℕ, ∀ (ts : List ℕ) (φ : Sentence) (rest : List ℕ),
      parseStructuredPaperPrime ts = some (φ, rest) →
        tokenSize φ ≤ 2 ^ (C * (ts.length - rest.length)) + C := by
  refine ⟨10, ?_⟩
  intro ts φ rest h
  rcases ts with _ | ⟨polarity, framed⟩
  · simp [parseStructuredPaperPrime] at h
  rw [parseStructuredPaperPrime] at h
  split at h <;> try contradiction
  rename_i hpol
  rcases hr : readStructuredLength framed with _ | ⟨n, payload⟩
  · simp [hr] at h
  rw [hr] at h
  simp only [Option.bind_some] at h
  split at h <;> try contradiction
  rename_i hlen
  rcases hp : parseStructuredArithmeticFormula n (payload.take n) with _ | ⟨code, r⟩
  · simp [hp] at h
  rw [hp] at h
  rcases r with _ | ⟨x, xs⟩
  · change (if List.getD payload n 0 = 19 then
        some (Formula.atom (Nat.pair 5 (Nat.pair polarity code)), payload.drop (n + 1))
      else none) = some (φ, rest) at h
    by_cases hterm : payload.getD n 0 = 19
    · rw [if_pos hterm] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
      -- the consumed block has at least `n + 2` tokens
      have hshape := readStructuredLength_shape hr
      have hL : n + 2 ≤ (polarity :: framed).length - (payload.drop (n + 1)).length := by
        rw [hshape]
        simp only [List.length_cons, List.length_append, List.length_replicate, List.length_drop]
        omega
      generalize (polarity :: framed).length - (payload.drop (n + 1)).length = L at hL ⊢
      -- the formula code
      have htree := (parseStructured_bounds n).2.2 _ _ _ hp
      have hcode : code < 4 ^ (2 ^ (10 * n + 5)) := by
        have := htree.lt_pow (two_le_termDigits n)
        rwa [four_pow_mul_termDigits] at this
      generalize hK : 2 ^ (10 * n + 5) = K at hcode
      have hK2 : 2 ≤ K := by
        rw [← hK]
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (10 * n + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
      -- the atom index
      have hpol' : polarity < 4 ^ K := lt_pow_mono (show polarity < 4 ^ 1 by omega) (by omega)
      have h1 : Nat.pair polarity code < 4 ^ (2 * K) := pair_lt_pow_of_lt hpol' hcode
      have h2 : Nat.pair 5 (Nat.pair polarity code) + 1 < 4 ^ (2 * (2 * K)) :=
        pair_small_succ_lt_pow (by norm_num) h1 (by omega)
      have h3 : Nat.pair 5 (Nat.pair polarity code) + 5 < 4 ^ (2 * (2 * K) + 1) := by
        rw [pow_succ]
        have := Nat.one_le_pow (2 * (2 * K)) 4 (by norm_num)
        omega
      have hdig := length_natDigits4_le_of_lt_pow h3
      rw [tokenSize_atom]
      -- `4 K + 2 = 2 ^ (10 n + 7) + 2 ≤ 2 ^ (10 L) + 10`
      have h4K : 4 * K = 2 ^ (10 * n + 7) := by
        rw [← hK, pow_succ, pow_succ]; ring
      have hmono : 2 ^ (10 * n + 7) ≤ 2 ^ (10 * L) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · rw [if_neg hterm] at h
      contradiction
  · simp at h

end Cleanroom.Bli.BliFound
