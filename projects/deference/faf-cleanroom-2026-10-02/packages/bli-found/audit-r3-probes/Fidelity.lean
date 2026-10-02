import Cleanroom.Bli.BliFound.Size

/-!
# `bli-found` — audit round 3, lens `fidelity`: probe (part 1, `Size` only)

Not imported by the library. Elaborated with `scripts/lean-check` against the package as left by
repair round 2 (14 modules, 897 declarations, gate PASS). Imports only `Size`: FAF's
semantic-extension modules cost about 3 GB to load and crawl inside the memory slice, so this
part states everything over the *literal* index of a tag-`4` handle, and part 2
(`FidelityAlias.lean`, heavy imports) proves by `rfl` that these literals are FAF's
`semanticPrimeCode`/`semanticPrimeSentence`/`semanticQuoteSchema`/`semanticQuoteLeaf`/
`semanticHandleLUVSeq` and ties the alias to the package's own `quoteLuv`.

**FAF's definitions, verbatim** (`Construction/SemanticExtension/Prime.lean`, `Quote.lean`;
`Construction/Knowledge/Syntax.lean:230` for `semanticPrimeTag = 4`):
`semanticPrimeCode schema input := Nat.pair semanticPrimeTag (Nat.pair schema input)`,
`semanticPrimeSentence schema input := Formula.atom (semanticPrimeCode schema input)`,
`semanticQuoteSchema code := Nat.pair 2 code`,
`semanticQuoteLeaf code input := semanticPrimeSentence (semanticQuoteSchema code) input`,
`semanticHandleLUVSeq schema n : LUV where gt r := semanticPrimeSentence schema (Nat.pair n ⌜r⌝)`,
and `semanticQuoteLeaf_reflected : v.ConsistentWithTheory semanticQuoteDP → (v.Holds
(semanticQuoteLeaf code input) ↔ v.Holds (quoteAtom (Nat.pair code input)))`.

**What it shows.** `Size.atomDay` reads `0` off every tag-`4` handle, although the tag-`4`
families quote market days (aliases of tag-`2` quotation atoms; day-indexed source/product LUV
handles with the day first in `input`). So the alias of a day-`m` quote lies in `Sminus m m` for
every large `m` (`quoteAlias_mem_Sminus_self`) for every selector code `c` — in particular for
`c := (marketQuoteCode T).code`, the package's own market quote code (part 2) — while the tag-`2`
quote it aliases lies in no `Sminus n m` (the package's `StateSentence.quoteAt_notMem_Sminus`;
part 2 for the single threshold). This is the round-2 tag-`3` pattern on tag `4`, and it
falsifies the universal direction claim "on every atom of a FAF-allocated family `atomDay a ≥`
the day it quotes" (F-14, the D3 ledger row, the `atomDay` docstring after repair round 2).
-/

namespace AuditR3

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-- The index of a tag-`4` semantic handle (FAF's `semanticPrimeCode`, part 2 `rfl`). -/
def handleCode (schema input : ℕ) : ℕ := Nat.pair 4 (Nat.pair schema input)

/-- The handle as a sentence (FAF's `semanticPrimeSentence`, part 2 `rfl`). -/
def handle (schema input : ℕ) : Sentence := Formula.atom (handleCode schema input)

/-- The quotation-alias schema selector (FAF's `semanticQuoteSchema`, part 2 `rfl`). -/
def quoteSchema (code : ℕ) : ℕ := Nat.pair 2 code

/-! ## `atomDay` on tag-`4` handles -/

/-- `atomDay` reads `0` off every tag-`4` semantic handle, whatever its schema and input. -/
lemma atomDay_handle (schema input : ℕ) :
    ∀ a ∈ sentenceAtomCodes (handle schema input), atomDay a = 0 := by
  intro a ha
  simp only [handle, sentenceAtomCodes_atom, Finset.mem_singleton] at ha
  subst ha
  simp [atomDay, atomDayBase, handleCode, cleanroomBaseTag]

/-- In particular off every quotation alias `handle (quoteSchema code) input`
(`= semanticQuoteLeaf code input`). -/
lemma atomDay_quoteAlias (code input : ℕ) :
    ∀ a ∈ sentenceAtomCodes (handle (quoteSchema code) input), atomDay a = 0 :=
  atomDay_handle _ _

/-- And off the day-`n` threshold `handle schema ⟨n, ⌜r⌝⟩` of every handle LUV family
(`= (semanticHandleLUVSeq schema n).gt r`), whose input packs the day first. -/
lemma atomDay_handleLUV_gt (schema n : ℕ) (r : ℚ) :
    ∀ a ∈ sentenceAtomCodes (handle schema (Nat.pair n (Encodable.encode r))), atomDay a = 0 :=
  atomDay_handle _ _

/-- A tag-`4` handle lies in `Sminus n m` as soon as it is small on day `n`, for every `m ≥ 1`. -/
lemma handle_mem_Sminus {n m schema input : ℕ} (hm : 0 < m)
    (hs : SmallOn n (handle schema input)) : handle schema input ∈ Sminus n m := by
  rw [mem_Sminus]
  exact ⟨hs, fun a ha => by rw [atomDay_handle schema input a ha]; exact hm⟩

/-- Every sentence is small from day `tokenSize` on (the package's `State.smallOn_tokenSize`,
re-proved to keep the imports to `Size`). -/
lemma smallOn_tokenSize' (φ : Sentence) : SmallOn (tokenSize φ) φ := by
  unfold SmallOn sizeBound
  calc tokenSize φ ≤ 2 ^ tokenSize φ := Nat.lt_two_pow_self.le
    _ ≤ 2 ^ (2 ^ tokenSize φ) := Nat.pow_le_pow_right (by norm_num) Nat.lt_two_pow_self.le

/-- The alias of a day-`m` quote lies in `Sminus k m` for some `k`, for every `m ≥ 1`. -/
lemma quoteAlias_mem_Sminus_exists (code m e s : ℕ) (hm : 0 < m) :
    ∃ k, handle (quoteSchema code) (Nat.pair (Nat.pair m e) s) ∈ Sminus k m :=
  ⟨_, handle_mem_Sminus hm (smallOn_tokenSize' _)⟩

/-- The day-`n` threshold of a handle LUV family lies in `Sminus k n` for some `k`, `n ≥ 1`. -/
lemma handleLUV_gt_mem_Sminus_exists (schema n : ℕ) (r : ℚ) (hn : 0 < n) :
    ∃ k, handle schema (Nat.pair n (Encodable.encode r)) ∈ Sminus k n :=
  ⟨_, handle_mem_Sminus hn (smallOn_tokenSize' _)⟩

/-! ## Non-vacuity at the scope day itself: the alias is in `Sminus m m` for all large `m` -/

/-- `Nat.pair` of two numbers `≤ X^k` is `≤ X^(2k+2)` (`X ≥ 2`). -/
lemma pair_le_pow {a b X k : ℕ} (hX : 2 ≤ X) (ha : a ≤ X ^ k) (hb : b ≤ X ^ k) :
    Nat.pair a b ≤ X ^ (2 * k + 2) := by
  have hXk : 1 ≤ X ^ k := Nat.one_le_pow _ _ (by omega)
  have hmax : max a b ≤ X ^ k := max_le ha hb
  calc Nat.pair a b ≤ (max a b + 1) ^ 2 := (Nat.pair_lt_max_add_one_sq a b).le
    _ ≤ (2 * X ^ k) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    _ = 4 * (X ^ k) ^ 2 := by ring
    _ ≤ X ^ 2 * (X ^ k) ^ 2 := Nat.mul_le_mul_right _ (by nlinarith)
    _ = X ^ (2 * k + 2) := by ring

/-- The index of the alias of a day-`m` quote is at most `X^46` with `X := c + e + s + m + 4`
(`c` the selector code, `e = ⌜φ⌝`, `s = ⌜r⌝`). -/
lemma alias_index_le (c e s m : ℕ) :
    handleCode (quoteSchema c) (Nat.pair (Nat.pair m e) s) ≤ (c + e + s + m + 4) ^ 46 := by
  unfold handleCode quoteSchema
  set X := c + e + s + m + 4 with hX
  have hX2 : 2 ≤ X := by omega
  have hm : m ≤ X ^ 1 := by rw [pow_one]; omega
  have he : e ≤ X ^ 1 := by rw [pow_one]; omega
  have hs : s ≤ X ^ 1 := by rw [pow_one]; omega
  have hc : c ≤ X ^ 1 := by rw [pow_one]; omega
  have h2 : 2 ≤ X ^ 1 := by rw [pow_one]; omega
  have h4 : 4 ≤ X ^ 1 := by rw [pow_one]; omega
  have p1 : Nat.pair m e ≤ X ^ 4 := by simpa using pair_le_pow hX2 hm he
  have hs' : s ≤ X ^ 4 := le_trans hs (Nat.pow_le_pow_right (by omega) (by norm_num))
  have p2 : Nat.pair (Nat.pair m e) s ≤ X ^ 10 := by simpa using pair_le_pow hX2 p1 hs'
  have q1 : Nat.pair 2 c ≤ X ^ 4 := by simpa using pair_le_pow hX2 h2 hc
  have q1' : Nat.pair 2 c ≤ X ^ 10 :=
    le_trans q1 (Nat.pow_le_pow_right (by omega) (by norm_num))
  have p3 : Nat.pair (Nat.pair 2 c) (Nat.pair (Nat.pair m e) s) ≤ X ^ 22 := by
    simpa using pair_le_pow hX2 q1' p2
  have h4' : 4 ≤ X ^ 22 := le_trans h4 (Nat.pow_le_pow_right (by omega) (by norm_num))
  simpa using pair_le_pow hX2 h4' p3

/-- `sizeBound (n + 1) = (sizeBound n)^2` (the package's `Witnesses.sizeBound_succ`, re-proved
to keep the imports to `Size`). -/
lemma sizeBound_succ' (n : ℕ) : sizeBound (n + 1) = sizeBound n * sizeBound n := by
  unfold sizeBound
  rw [pow_succ, pow_mul, sq]

/-- `47 m + 1 < sizeBound m` for `m ≥ 3`. -/
lemma lt_sizeBound {m : ℕ} (hm : 3 ≤ m) : 47 * m + 1 < sizeBound m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [sizeBound]
  | succ k hk ih =>
      rw [sizeBound_succ']
      have h1 : 47 * k + 2 ≤ sizeBound k := by omega
      have h2 : 2 ≤ sizeBound k := two_le_sizeBound k
      calc 47 * (k + 1) + 1 = 47 * k + 48 := by ring
        _ < (47 * k + 2) * 2 := by omega
        _ ≤ sizeBound k * sizeBound k := Nat.mul_le_mul h1 h2

/-- The alias of a day-`m` quote (selector `c`, `e = ⌜φ⌝`, `s = ⌜r⌝`) is small on day `m` for
every `m ≥ c + e + s + 4`. -/
lemma smallOn_quoteAlias {c e s m : ℕ} (hm : c + e + s + 4 ≤ m) :
    SmallOn m (handle (quoteSchema c) (Nat.pair (Nat.pair m e) s)) := by
  unfold SmallOn handle
  rw [tokenSize_atom]
  set X := c + e + s + m + 4 with hX
  set K := sizeBound m with hK
  have hm3 : 3 ≤ m := by omega
  have hK1 : 47 * m + 1 < K := lt_sizeBound hm3
  have hK2 : 2 ≤ K := two_le_sizeBound m
  have hXm : X ≤ 2 * m := by omega
  have hidx : handleCode (quoteSchema c) (Nat.pair (Nat.pair m e) s) ≤ X ^ 46 :=
    alias_index_le c e s m
  have hX7 : 7 ≤ X := by omega
  -- index + 5 < X^47
  have h47 : handleCode (quoteSchema c) (Nat.pair (Nat.pair m e) s) + 5 < X ^ 47 := by
    have hle : X ≤ X ^ 46 := le_self_pow (by omega) (by norm_num)
    have hpow : X ^ 47 = X * X ^ 46 := by ring
    rw [hpow]
    have h2 : 2 * X ^ 46 ≤ X * X ^ 46 := Nat.mul_le_mul_right _ (by omega)
    omega
  -- X^47 ≤ 2^(47 X)
  have h2X : X ^ 47 ≤ 2 ^ (47 * X) := by
    have : X ≤ 2 ^ X := Nat.lt_two_pow_self.le
    calc X ^ 47 ≤ (2 ^ X) ^ 47 := Nat.pow_le_pow_left this 47
      _ = 2 ^ (X * 47) := by rw [← pow_mul]
      _ = 2 ^ (47 * X) := by rw [Nat.mul_comm]
  -- 2^(47 X) < 4^(K - 1)
  have h4K : 2 ^ (47 * X) < 4 ^ (K - 1) := by
    have h4 : (4 : ℕ) ^ (K - 1) = 2 ^ (2 * (K - 1)) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    rw [h4]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hdig := length_natDigits4_le_of_lt_pow (lt_of_lt_of_le h47 (le_trans h2X h4K.le))
  omega

/-- **The alias of a day-`m` quote lies in the scope of faith at day `m`**, for every `m` from
a threshold depending only on the selector code `c`, `e = ⌜φ⌝` and `s = ⌜r⌝`:
`handle (quoteSchema c) ⟨⟨m, e⟩, s⟩ ∈ Sminus m m` — i.e. `semanticQuoteLeaf c ⟨⟨m, e⟩, s⟩ ∈
Sminus m m` (part 2 `rfl`). With `c := (marketQuoteCode T).code` this is the alias of the
package's own threshold literal `(quoteLuv T m φ).gt r` (part 2), which itself lies in no
`Sminus n m`. -/
theorem quoteAlias_mem_Sminus_self (c e s : ℕ) :
    ∃ M, ∀ m ≥ M, handle (quoteSchema c) (Nat.pair (Nat.pair m e) s) ∈ Sminus m m :=
  ⟨c + e + s + 4, fun m hm => handle_mem_Sminus (by omega) (smallOn_quoteAlias hm)⟩

end AuditR3
