import Cleanroom.Bli.BliFound.Tags
import LogicalInduction.Framework.Criterion
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Finite.Basic

/-!
# `bli-found` · Size: the size measure and the small/large split (F1's objects)

**D3 / T4** of the mandate. The size of a sentence is what FAF's `def:ec` charges a trader that
spells it canonically: `EfficientlyComputable` meters a trader by the *bits* its `FP` machine
writes on the unary day, `strategyOfOutput n w = strategyOfTokens n (unRpn (undigitize (bitsToDigits w)))`,
so a token `t` costs `(natDigits4 t).length + 1` self-delimiting base-4 digits and a sentence
slot is the RPN run `rpn φ`. Hence:

* `tokenSize φ = (digitize (rpn φ)).length` — the canonical digit-metered size (chosen over
  "shortest name", which is not computable by structural recursion, and over `Encodable.encode φ`
  or its bit length, which is exponential in depth and would make the bridge lemma false or the
  split useless — mandate D3, T1 trap (ii));
* `sizeBound n = 2 ^ (2 ^ n)`, `SmallOn n φ := tokenSize φ ≤ sizeBound n` — decidable, monotone
  in `n`; `smallSet n` the finite set of day-`n` small sentences; `Sminus n m` the day-`n` small
  sentences quoting no market day `≥ m`.

**Why doubly exponential.** `parseRpn` accepts three spellings of a sentence slot: the canonical
run, the Gödel escape `1 :: c`, and the structured paper-prime escape whose tag-5 atom index can
be *exponential* in the escape's length. A polynomial-length stream can therefore name an atom
with `2^{Θ(n^d)}` digits, and the bridge lemma survives only because `2^{c n^d} ≤ 2^{2^n}`
eventually (mandate D3; findings F-4).

**Rejected variant** (bli-paper-031, bli-soto-a-002 reading B): "small on day `n` = traded by
some trader of the LIA by day `n`" — circular for an arbitrary market, not formalized
(Known issue 5).

**Day 0.** `sizeBound 0 = 2`, and the only sentence of size `≤ 2` is `⊥` (every atom costs
`≥ 3`: `a + 5 ≥ 5` has two base-4 digits). So `smallSet 0 = {⊥}` and the counting lemma
`sizeBound_lt_card_smallSet` holds from day `1` on; nothing downstream needs day `0`.

Sources: [[bli-program]] §2.1 (corrected, see findings); bli-paper-031; bli-slides-030;
bli-soto-a-002 reading A; mandate D3.
-/

namespace Cleanroom.Bli.BliFound

open LogicalInduction LO.Propositional

/-! ## Digit blocks -/

/-- `length_tokenBlock`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma length_tokenBlock (t : ℕ) : (tokenBlock t).length = (natDigits4 t).length + 1 := by
  simp [tokenBlock]

/-- `digitize_nil`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma digitize_nil : digitize ([] : List ℕ) = [] := rfl

/-- `digitize_cons`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma digitize_cons (t : ℕ) (ts : List ℕ) : digitize (t :: ts) = tokenBlock t ++ digitize ts := by
  simp [digitize]

/-- `length_digitize_cons`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma length_digitize_cons (t : ℕ) (ts : List ℕ) :
    (digitize (t :: ts)).length = (natDigits4 t).length + 1 + (digitize ts).length := by
  simp [digitize_cons]

/-- Every token block has at least one digit, so a token stream is no longer than its digit
stream.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma length_le_length_digitize (ts : List ℕ) : ts.length ≤ (digitize ts).length := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
      rw [length_digitize_cons, List.length_cons]
      omega

/-- Each token's block is a sublist of the digit stream.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma length_natDigits4_add_one_le_length_digitize {t : ℕ} {ts : List ℕ} (ht : t ∈ ts) :
    (natDigits4 t).length + 1 ≤ (digitize ts).length := by
  induction ts with
  | nil => simp at ht
  | cons u ts ih =>
      rw [length_digitize_cons]
      rcases List.mem_cons.mp ht with rfl | ht
      · omega
      · have := ih ht
        omega

/-! ## `natDigits4` and base-4 logarithms -/

/-- `n < 4 ^ (number of base-4 digits of n)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lt_pow_length_natDigits4 (n : ℕ) : n < 4 ^ (natDigits4 n).length := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      cases n with
      | zero => simp [natDigits4]
      | succ m =>
          rw [natDigits4, List.length_cons, pow_succ]
          have hq := ih ((m + 1) / 4) (Nat.div_lt_self (Nat.succ_pos m) (by norm_num))
          have hmod : (m + 1) % 4 + 4 * ((m + 1) / 4) = m + 1 := Nat.mod_add_div (m + 1) 4
          have hlt : (m + 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
          omega

/-- If `n < 4 ^ L` then `n` has at most `L` base-4 digits.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma length_natDigits4_le_of_lt_pow {n L : ℕ} (h : n < 4 ^ L) : (natDigits4 n).length ≤ L := by
  induction L generalizing n with
  | zero =>
      have : n = 0 := by simpa using h
      subst this
      simp [natDigits4]
  | succ L ih =>
      cases n with
      | zero => simp [natDigits4]
      | succ m =>
          rw [natDigits4, List.length_cons]
          have hdiv : (m + 1) / 4 < 4 ^ L := by
            rw [Nat.div_lt_iff_lt_mul (by norm_num)]
            rw [pow_succ] at h
            omega
          have := ih hdiv
          omega

/-- A nonzero number has at least one digit.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma one_le_length_natDigits4 {n : ℕ} (hn : n ≠ 0) : 1 ≤ (natDigits4 n).length := by
  cases n with
  | zero => exact absurd rfl hn
  | succ m => rw [natDigits4, List.length_cons]; omega

/-- The digit count of a nonzero number is `Nat.log 4 n + 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma length_natDigits4_eq_log {n : ℕ} (hn : n ≠ 0) :
    (natDigits4 n).length = Nat.log 4 n + 1 := by
  have h1 := one_le_length_natDigits4 hn
  have hlt := lt_pow_length_natDigits4 n
  have hge : 4 ^ ((natDigits4 n).length - 1) ≤ n := by
    by_contra hcon
    rw [not_le] at hcon
    have := length_natDigits4_le_of_lt_pow hcon
    omega
  have hlog : Nat.log 4 n = (natDigits4 n).length - 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow hge (by rwa [Nat.sub_add_cancel h1])
  omega

/-! ## The size measure -/

/-- **Digit-metered length of the canonical RPN run of `φ`**: what FAF's `def:ec` charges a
trader that spells `φ` canonically, `(digitize (rpn φ)).length = Σ_{t ∈ rpn φ} ((natDigits4 t).length + 1)`.
Source: [[bli-program]] §2.1 (corrected: see findings F-4); bli-paper-031; mandate D3
Kind: D
Fidelity: variant: canonical digit-metered size, not "shortest name" (see module docstring) -/
def tokenSize (φ : Sentence) : ℕ := (digitize (rpn φ)).length

/-- `tokenSize_atom`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma tokenSize_atom (a : ℕ) :
    tokenSize (Formula.atom a) = (natDigits4 (a + 5)).length + 1 := by
  simp [tokenSize, rpn, digitize_cons]

/-- `tokenSize_falsum`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma tokenSize_falsum : tokenSize (⊥ : Sentence) = 1 := by
  simp [tokenSize, rpn, digitize_cons, natDigits4]

/-- `tokenSize_and`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma tokenSize_and (φ ψ : Sentence) :
    tokenSize (φ ⋏ ψ) = 2 + tokenSize φ + tokenSize ψ := by
  simp [tokenSize, rpn, digitize_cons, natDigits4]
  omega

/-- `tokenSize_or`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma tokenSize_or (φ ψ : Sentence) :
    tokenSize (φ ⋎ ψ) = 3 + tokenSize φ + tokenSize ψ := by
  simp [tokenSize, rpn, digitize_cons, natDigits4]
  omega

/-- `tokenSize_imp`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma tokenSize_imp (φ ψ : Sentence) :
    tokenSize (φ 🡒 ψ) = 2 + tokenSize φ + tokenSize ψ := by
  simp [tokenSize, rpn, digitize_cons, natDigits4]
  omega

/-- `tokenSize_neg`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tokenSize_neg (φ : Sentence) : tokenSize (∼φ) = 3 + tokenSize φ := by
  rw [Formula.neg_def, tokenSize_imp, tokenSize_falsum]
  omega

/-- `tokenSize_verum`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tokenSize_verum : tokenSize (⊤ : Sentence) = 4 := by
  change tokenSize ((⊥ : Sentence) 🡒 ⊥) = 4
  rw [tokenSize_imp, tokenSize_falsum]

/-- The RPN run of a sentence is nonempty.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma one_le_length_rpn (φ : Sentence) : 1 ≤ (rpn φ).length := by
  cases φ <;> simp [rpn]

/-- Every sentence has positive size.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma one_le_tokenSize (φ : Sentence) : 1 ≤ tokenSize φ :=
  le_trans (one_le_length_rpn φ) (length_le_length_digitize _)

/-- Every atom has size at least `3` (`a + 5 ≥ 5` has two base-4 digits).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma three_le_tokenSize_atom (a : ℕ) : 3 ≤ tokenSize (Formula.atom a) := by
  rw [tokenSize_atom]
  have : 2 ≤ (natDigits4 (a + 5)).length := by
    by_contra h
    rw [not_le] at h
    have := lt_pow_length_natDigits4 (a + 5)
    have : 4 ^ (natDigits4 (a + 5)).length ≤ 4 ^ 1 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  omega

/-- The RPN run is no longer than the size.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma length_rpn_le_tokenSize (φ : Sentence) : (rpn φ).length ≤ tokenSize φ :=
  length_le_length_digitize _

/-- Every token of the RPN run is below `4 ^ tokenSize φ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lt_pow_tokenSize_of_mem_rpn {φ : Sentence} {t : ℕ} (ht : t ∈ rpn φ) :
    t < 4 ^ tokenSize φ :=
  lt_of_lt_of_le (lt_pow_length_natDigits4 t)
    (Nat.pow_le_pow_right (by norm_num)
      (by have := length_natDigits4_add_one_le_length_digitize ht; unfold tokenSize; omega))

/-! ## The bound and the split -/

/-- **The day-`n` size bound** `2 ^ (2 ^ n)`: superpolynomial in the bit length of anything an
e.c. trader emits on day `n` (even through the structured escape, whose atoms have
`2^{O(n^d)}` digits), and — being a tower — enough that a written-out table over `smallSet m`
is large on day `m` (`stateAtom_large_of_writeOut`). Provisional in the sense of
[[bli-program]] §2.1: any computable superpolynomial bound that dominates the trading firm's
budget would do; every dependent tolerates a change here, but none is expected.
Source: [[bli-program]] §2.1; mandate D3
Kind: D
Fidelity: exact -/
def sizeBound (n : ℕ) : ℕ := 2 ^ (2 ^ n)

/-- `sizeBound_mono`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sizeBound_mono {n n' : ℕ} (h : n ≤ n') : sizeBound n ≤ sizeBound n' :=
  Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) h)

/-- `two_le_sizeBound`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma two_le_sizeBound (n : ℕ) : 2 ≤ sizeBound n := by
  unfold sizeBound
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 ^ n) := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_two_pow)

/-- `four_le_sizeBound`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma four_le_sizeBound {n : ℕ} (hn : 1 ≤ n) : 4 ≤ sizeBound n := by
  unfold sizeBound
  calc 4 = 2 ^ (2 ^ 1) := by norm_num
    _ ≤ 2 ^ (2 ^ n) := Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)

/-- **Small on day `n`**: `tokenSize φ ≤ sizeBound n`. Decidable by structural recursion (so a
polynomial-time rewrite certificate can decide it), monotone in `n`.
Source: [[bli-program]] §2.1; bli-paper-031; bli-slides-030; mandate D3
Kind: D
Fidelity: variant: canonical digit-metered size (see `tokenSize`); the "traded by some trader"
reading is rejected (Known issue 5) -/
def SmallOn (n : ℕ) (φ : Sentence) : Prop := tokenSize φ ≤ sizeBound n

/-- `SmallOn.decidable`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance SmallOn.decidable (n : ℕ) (φ : Sentence) : Decidable (SmallOn n φ) :=
  inferInstanceAs (Decidable (tokenSize φ ≤ sizeBound n))

/-- Smallness is monotone in the day.
Source: mandate D3
Kind: L
Fidelity: exact -/
lemma SmallOn.mono {n n' : ℕ} (h : n ≤ n') {φ : Sentence} (hφ : SmallOn n φ) : SmallOn n' φ :=
  le_trans hφ (sizeBound_mono h)

/-- `smallOn_falsum`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma smallOn_falsum (n : ℕ) : SmallOn n (⊥ : Sentence) := by
  unfold SmallOn
  rw [tokenSize_falsum]
  exact le_trans (by norm_num) (two_le_sizeBound n)

/-! ## Finiteness -/

/-- The sentences of size `≤ K` form a finite set: by strong induction on `K`, they are the
atoms with `a + 5 < 4 ^ K`, `⊥`, and the connectives applied to sentences of size `< K`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma finite_tokenSize_le (K : ℕ) : {φ : Sentence | tokenSize φ ≤ K}.Finite := by
  induction K using Nat.strong_induction_on with
  | _ K ih =>
      rcases Nat.eq_zero_or_pos K with rfl | hK
      · refine Set.finite_empty.subset ?_
        intro φ hφ
        have := one_le_tokenSize φ
        simp only [Set.mem_setOf_eq] at hφ
        omega
      · -- the pieces
        have hatoms : ({φ : Sentence | ∃ a < 4 ^ K, φ = Formula.atom a} : Set Sentence).Finite := by
          refine ((Set.finite_lt_nat (4 ^ K)).image (fun a => (Formula.atom a : Sentence))).subset ?_
          rintro φ ⟨a, ha, rfl⟩
          exact ⟨a, ha, rfl⟩
        have hsub : {φ : Sentence | tokenSize φ ≤ K - 1}.Finite := ih (K - 1) (by omega)
        have hand := hsub.image2 (fun φ ψ : Sentence => φ ⋏ ψ) hsub
        have hor := hsub.image2 (fun φ ψ : Sentence => φ ⋎ ψ) hsub
        have himp := hsub.image2 (fun φ ψ : Sentence => φ 🡒 ψ) hsub
        refine ((((hatoms.union (Set.finite_singleton (⊥ : Sentence))).union hand).union hor).union
          himp).subset ?_
        intro φ hφ
        simp only [Set.mem_setOf_eq] at hφ
        cases φ with
        | atom a =>
            left; left; left; left
            refine ⟨a, ?_, rfl⟩
            have h1 := lt_pow_length_natDigits4 (a + 5)
            have h2 : (natDigits4 (a + 5)).length + 1 ≤ K := by simpa using hφ
            calc a < a + 5 := by omega
              _ < 4 ^ (natDigits4 (a + 5)).length := h1
              _ ≤ 4 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
        | falsum => left; left; left; right; rfl
        | and φ ψ =>
            left; left; right
            rw [show (Formula.and φ ψ : Sentence) = φ ⋏ ψ from rfl, tokenSize_and] at hφ
            exact ⟨φ, by simp only [Set.mem_setOf_eq]; omega, ψ,
              by simp only [Set.mem_setOf_eq]; omega, rfl⟩
        | or φ ψ =>
            left; right
            rw [show (Formula.or φ ψ : Sentence) = φ ⋎ ψ from rfl, tokenSize_or] at hφ
            exact ⟨φ, by simp only [Set.mem_setOf_eq]; omega, ψ,
              by simp only [Set.mem_setOf_eq]; omega, rfl⟩
        | imp φ ψ =>
            right
            rw [show (Formula.imp φ ψ : Sentence) = φ 🡒 ψ from rfl, tokenSize_imp] at hφ
            exact ⟨φ, by simp only [Set.mem_setOf_eq]; omega, ψ,
              by simp only [Set.mem_setOf_eq]; omega, rfl⟩

/-- The day-`n` small sentences form a finite set.
Source: mandate D3
Kind: L
Fidelity: exact -/
lemma smallSet_finite (n : ℕ) : {φ : Sentence | SmallOn n φ}.Finite :=
  finite_tokenSize_le (sizeBound n)

/-- **The finite set of day-`n` small sentences** `{φ | SmallOn n φ}`.
Source: [[bli-program]] §2.1; mandate D3
Kind: D
Fidelity: exact -/
noncomputable def smallSet (n : ℕ) : Finset Sentence := (smallSet_finite n).toFinset

/-- Membership in `smallSet n` is `SmallOn n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mem_smallSet {n : ℕ} {φ : Sentence} : φ ∈ smallSet n ↔ SmallOn n φ :=
  Set.Finite.mem_toFinset _

/-- `smallSet_mono`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma smallSet_mono {n n' : ℕ} (h : n ≤ n') : smallSet n ⊆ smallSet n' := by
  intro φ hφ
  rw [mem_smallSet] at hφ ⊢
  exact hφ.mono h

/-- `falsum_mem_smallSet`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma falsum_mem_smallSet (n : ℕ) : (⊥ : Sentence) ∈ smallSet n :=
  mem_smallSet.mpr (smallOn_falsum n)

/-! ## Counting: the small set outgrows the bound -/

/-- `j + 6 < 4 ^ j` for `j ≥ 3`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma add_six_lt_four_pow {j : ℕ} (hj : 3 ≤ j) : j + 6 < 4 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j _ ih => rw [pow_succ]; omega

/-- **The small set is larger than the bound** (from day `1`): there are more than `sizeBound n`
day-`n`-small sentences — already among the atoms `a ≤ sizeBound n`, each of size
`(natDigits4 (a + 5)).length + 1 ≤ sizeBound n`. This is what makes a literal write-out of a
table over `smallSet m` longer than `sizeBound m` (`State.stateAtom_large_of_writeOut`). Day `0`
is excluded: `smallSet 0 = {⊥}` has one element and `sizeBound 0 = 2`.
Source: mandate D3 (the counting behind bli-paper-032's "longer than every sentence it prices")
Kind: P
Fidelity: weaker: from day `1` on (day `0` is a genuine exception, see module docstring)
Hyps: (a) -/
theorem sizeBound_lt_card_smallSet {n : ℕ} (hn : 1 ≤ n) : sizeBound n < (smallSet n).card := by
  set K := sizeBound n with hKdef
  have hK4 : 4 ≤ K := four_le_sizeBound hn
  -- the atoms `a ≤ K` are all small on day `n`
  have hsmall : ∀ a ≤ K, SmallOn n (Formula.atom a) := by
    intro a ha
    unfold SmallOn
    rw [tokenSize_atom]
    have hbound : a + 5 < 4 ^ (K - 1) := by
      have := add_six_lt_four_pow (j := K - 1) (by omega)
      omega
    have := length_natDigits4_le_of_lt_pow hbound
    omega
  have hsub : (Finset.range (K + 1)).image (fun a => (Formula.atom a : Sentence)) ⊆ smallSet n := by
    intro φ hφ
    rw [Finset.mem_image] at hφ
    obtain ⟨a, ha, rfl⟩ := hφ
    rw [Finset.mem_range] at ha
    exact mem_smallSet.mpr (hsmall a (by omega))
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun a b h => Formula.atom.inj h), Finset.card_range] at hcard
  omega

/-! ## `Sminus`: small sentences quoting no market day `≥ m` -/

/-- **The day an atom index refers to, before the old-language unwrap** (`atomDay` below adds
the tag-`6` case). Read per FAF's global tag table (`ComputationClaimKind.godelCode`,
`Construction/Knowledge/Syntax.lean`) and the run's registry (`freshAtom`):

* tag `≥ cleanroomBaseTag` (the run's families): the **first payload component**, by the registry
  convention on `freshAtom`;
* tag `3` (FAF's quoted products `productAtom n r = ⌜Xₙ · Wₙ > r⌝`, index
  `Nat.pair 3 (Nat.pair n ⌜r⌝)`, `Construction/Quotation/ProductDefinition.lean`): the first
  payload component, i.e. the product's day `n` (`PaperInstances.atomDay_productAtom`);
* tag `2` (FAF's quotation claims, index `Nat.pair 2 (Nat.pair ⌜Pos⌝ (Nat.pair ⌜Neg⌝ w))` with
  `w = ⟨code, input⟩`, `encode_quoteAtom`): the **whole packed `input`** — a modelling choice
  `(c)`, since the day sits inside `input` differently per quote family (`input = n` for
  `BooleanQuoteCode`, `⟨n, ⌜r⌝⟩` for `RationalQuoteCode`, `⟨⟨m, ⌜φ⌝⟩, ⌜r⌝⟩` for this run's
  `StateSentence.quoteAt`), and the packed input is `≥` every component, so the reading is
  `≥` the true day;
* every other tag (`0`/`1` halting claims, `4` semantic handles, `5` first-order primes, `7` bit
  atoms — none of which names a market day in FAF's table): `0`.

Until repair round 2 the tag-`3` case read `0`, so `Sminus m m` admitted a day-`n` product atom
for every `n ≥ m` (audit r2 fidelity B1, probe `productAtom_mem_Sminus_self`) and the
under-approximation claim below was false for product atoms.
Source: mandate D3.3; FAF tag table; audit r1 (fidelity §3.2, adversarial N3); audit r2 (fidelity B1)
Kind: D
Fidelity: variant: (c) on tag 2 (reads a number `≥` the day) -/
def atomDayBase (a : ℕ) : ℕ :=
  if cleanroomBaseTag ≤ a.unpair.1 ∨ a.unpair.1 = 3 then a.unpair.2.unpair.1
  else if a.unpair.1 = 2 then a.unpair.2.unpair.2.unpair.2.unpair.2
  else 0

/-- **The day an atom index refers to.** `atomDayBase` after unwrapping one old-language copy:
FAF's semantic extension renames every atom `a` of the pre-extension language to
`oldAtom a = Nat.pair 6 a` (`Construction/SemanticExtension/LanguageCopy.lean`), so a tag-`6` atom
refers to whatever day its payload atom does (`atomDay_pair_six`). One level only: FAF copies the
pre-extension language once, and a doubly wrapped copy (which FAF never builds) reads day `0`.

**Direction of the `(c)`.** On every atom of the FAF-allocated families (tags `0`–`7`, `9+`; the
advice atoms of `FinitePerturbationCounterexample` live over their own market and are not in
scope), `atomDay a` is `≥` the day the atom quotes — equal for the run's families, tag `3` and
their tag-`6` copies (`atomDay_freshAtomCode`, `PaperInstances.atomDay_productAtom`,
`atomDay_pair_six`); the packed input, hence `≥` the day, for tag `2`
(`StateSentence.atomDay_quotationClaimCode`); and `0` for the families that name no market day.
So `atomDay a < m` implies the atom quotes no day `≥ m`: **`Sminus n m` under-approximates the
prose scope** ("quoting no market day `≥ m`", [[bli-program]] §2.1; the Notion reading of
bli-soto-a-003) and every predicate quantified over it (`E2x`, `E2i`, `E3`, `E3fin`) is
correspondingly *weaker* than the source, never inconsistent with it. The exclusion is total on
the quote families this run builds: `Sminus m m` contains no interval quote of any day
(`StateSentence.quoteAt_notMem_Sminus`, findings F-14) and no product atom of any day `≥ m`
(`PaperInstances.productAtom_notMem_Sminus`). Nothing in this package's theorems depends on the
tag-`2` convention.
Source: mandate D3.3; FAF tag table; audit r1 (fidelity §3.2, adversarial N3); audit r2 (fidelity B1)
Kind: D
Fidelity: variant: (c) the tag-2 day reading under-approximates the scope; tags 3 and 6 read exactly (repair round 2) -/
def atomDay (a : ℕ) : ℕ :=
  if a.unpair.1 = 6 then atomDayBase a.unpair.2 else atomDayBase a

/-- The base day of a fresh atom is the first payload component.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma atomDayBase_freshAtomCode (f d r : ℕ) :
    atomDayBase (freshAtomCode f (Nat.pair d r)) = d := by
  unfold atomDayBase freshAtomCode cleanroomBaseTag
  simp only [Nat.unpair_pair]
  rw [if_pos (Or.inl (by omega))]

/-- The day of a fresh atom is the first payload component.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma atomDay_freshAtomCode (f d r : ℕ) : atomDay (freshAtomCode f (Nat.pair d r)) = d := by
  unfold atomDay
  rw [if_neg (by simp only [freshAtomCode, cleanroomBaseTag, Nat.unpair_pair]; omega)]
  exact atomDayBase_freshAtomCode f d r

/-- An atom whose tag is not `6` reads its base day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atomDay_of_tag_ne_six {a : ℕ} (h : a.unpair.1 ≠ 6) : atomDay a = atomDayBase a := by
  unfold atomDay
  rw [if_neg h]

/-- **A tag-`6` old-language copy reads the day of the atom it copies**: `atomDay (Nat.pair 6 a)
= atomDayBase a` (FAF's `oldAtom a = Nat.pair oldLanguageTag a`, `oldLanguageTag = 6`).
Source: FAF `Construction/SemanticExtension/LanguageCopy.lean` (`oldAtom`); audit r2 (fidelity B1)
Kind: L
Fidelity: exact (one level of copying) -/
lemma atomDay_pair_six (a : ℕ) : atomDay (Nat.pair 6 a) = atomDayBase a := by
  simp [atomDay]

/-- **`Sminus n m`**: the day-`n` small sentences all of whose atoms refer to days `< m` (E2x's
"scope of faith": the small sentences carrying no information about market states on or after
day `m`, the Notion reading of bli-soto-a-003). Under-approximates the prose scope (see
`atomDay`: the tag-2 reading is `≥` the day; every other FAF family with a day is read exactly).
Source: [[bli-program]] §2.1; bli-soto-a-003 (Notion reading); mandate D3.3
Kind: D
Fidelity: variant: (c) through `atomDay`'s tag-2 convention (a subset of the prose scope) -/
noncomputable def Sminus (n m : ℕ) : Finset Sentence :=
  (smallSet n).filter fun φ => ∀ a ∈ sentenceAtomCodes φ, atomDay a < m

/-- `mem_Sminus`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_Sminus {n m : ℕ} {φ : Sentence} :
    φ ∈ Sminus n m ↔ SmallOn n φ ∧ ∀ a ∈ sentenceAtomCodes φ, atomDay a < m := by
  simp [Sminus]

/-- `Sminus_subset_smallSet`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Sminus_subset_smallSet (n m : ℕ) : Sminus n m ⊆ smallSet n := Finset.filter_subset _ _

/-- `⊥` is in every `Sminus n m` (it has no atoms), so `Sminus m m ≠ ∅` and `E2x`'s scope is
never empty by a typing accident.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma falsum_mem_Sminus (n m : ℕ) : (⊥ : Sentence) ∈ Sminus n m := by
  rw [mem_Sminus]
  exact ⟨smallOn_falsum n, fun a ha => by simp at ha⟩

/-- A fresh atom of day `d` lies in `Sminus n m` iff it is small on day `n` and `d < m`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freshAtom_mem_Sminus_iff {n m f d r : ℕ} :
    freshAtom f (Nat.pair d r) ∈ Sminus n m ↔ SmallOn n (freshAtom f (Nat.pair d r)) ∧ d < m := by
  rw [mem_Sminus]
  simp

end Cleanroom.Bli.BliFound
