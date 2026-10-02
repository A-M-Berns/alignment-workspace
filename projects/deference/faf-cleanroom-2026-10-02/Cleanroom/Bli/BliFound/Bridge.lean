import Cleanroom.Bli.BliFound.Size
import Cleanroom.Bli.BliFound.Structured
import LogicalInduction.Framework.Emission.RpnSentence
import Complexitylib.Classes.P.Cobham.Internal

/-!
# `bli-found` · Bridge: the bridge lemma (F1, T1)

**The claim.** An efficiently computable trader eventually names only small sentences:
`EfficientlyComputable Tr → ∃ N, ∀ n ≥ N, ∀ φ, MentionedBy (Tr.strat n) φ → SmallOn n φ`,
where `MentionedBy s φ` is "`φ` is a traded sentence of `s`, or occurs as the sentence of a
price leaf `EF.price φ k` of some coefficient of `s`".

This is the *only* place the small/large split touches `def:ec`; every downstream "traders never
touch large sentences, so we may re-price them" (bli-paper-031's footnote, bli-slides-030) rests
on it. It is proved against FAF's actual metering — nothing about traders is assumed:

1. `EfficientlyComputable` unpacks to an `F ∈ Complexity.FP` with
   `Tr.strat n = strategyOfOutput n (F (unaryDay n))`; `output_length_poly_of_mem_FP` bounds
   `|F (unaryDay n)|` by a polynomial in `n`.
2. `strategyOfOutput n w = strategyOfTokens n (unRpn (undigitize (bitsToDigits w)))`. The digit
   stream has `|w| / 3` digits, the token stream `ts = undigitize ds` is no longer than the digit
   stream, and every token of `ts` is below `4 ^ |ds|`.
3. **Stream lemma** (`exists_token_of_mentionedBy`): every sentence mentioned by
   `strategyOfTokens n us` is `Encodable.decode c` for some token `c ∈ us` — the streaming
   decoder `EF.streamReadFrom` produces sentences only by decoding a token.
4. **Contraction lemma** (`mem_unRpn`): every token of `unRpn ts` is a token of `ts`, or `0`, or
   `Encodable.encode φ` for a `φ` parsed by `parseRpn` from a suffix of `ts`.
5. **Size bounds**: `tokenSize φ ≤ Encodable.encode φ` and
   `Encodable.decode c = some φ → Encodable.encode φ ≤ c` (so a Gödel-escaped or copied token
   `c` names a sentence of size `≤ c < 4 ^ (digits of c)`); and the **parse-size lemma**
   (`tokenSize_le_of_parseRpn`): a sentence `parseRpn` reads from `L` tokens has size
   `≤ 2 ^ (C · L') + C` where `L'` is the digit length of the consumed block — with the
   canonical spelling contributing its own block, the Gödel escape `1 :: c` contributing
   `c < 4 ^ digits(c)`, and the structured paper-prime escape contributing the bound
   `tokenSize_le_of_structured` on the codec of `Framework/Criterion.lean:1824–1894`, proved in
   `Structured.lean` (a tree-shape invariant that `negFormulaCode` preserves; it was OPEN in the
   first formalizer's version, findings F-4b).
6. Arithmetic: `2 ^ (C · p(n)) + C ≤ 2 ^ (2 ^ n)` eventually.

Sources: bli-paper-031 footnote; bli-slides-030; bli-soto-a-002 reading A; [[bli-program]] §2.1
(whose proof sketch has the gap described in `Size.lean`'s docstring); mandate T1.
-/

namespace Cleanroom.Bli.BliFound

open LogicalInduction LO.Propositional

/-! ## `MentionedBy` -/

/-- **`φ` is mentioned by the strategy `s`**: it is a traded sentence of `s`, or the sentence of a
price leaf `EF.price φ k` of one of its coefficients (`EF.priceQueries`). This is the interface
`bli-transfer` and `bli-overlay` state their re-pricing lemmas over.
Source: mandate T1
Kind: D
Fidelity: exact -/
def MentionedBy {n : ℕ} (s : Strategy n) (φ : Sentence) : Prop :=
  (∃ e, (e, φ) ∈ s.trades) ∨ ∃ p ∈ s.trades, ∃ k, (k, φ) ∈ p.1.priceQueries

/-! ## Size against the Gödel code -/

/-- `a + b ≤ Nat.pair a b`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma add_le_pair (a b : ℕ) : a + b ≤ Nat.pair a b := by
  unfold Nat.pair
  split_ifs with h
  · nlinarith
  · nlinarith

/-- `a + 2 ≤ Nat.pair 1 a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma add_two_le_pair_one (a : ℕ) : a + 2 ≤ Nat.pair 1 a := by
  unfold Nat.pair
  split_ifs with h
  · nlinarith
  · omega

/-- `n < 4 ^ (n + 1)`, hence at most `n + 1` base-4 digits.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma length_natDigits4_le_succ (n : ℕ) : (natDigits4 n).length ≤ n + 1 := by
  apply length_natDigits4_le_of_lt_pow
  have h1 : n < 4 ^ n := Nat.lt_pow_self (by norm_num)
  rw [pow_succ]
  omega

/-- The digit count of `a + 5` is at most `a + 2` (`a + 5 < 4 ^ (a + 2)`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma length_natDigits4_add_five (a : ℕ) : (natDigits4 (a + 5)).length ≤ a + 2 := by
  apply length_natDigits4_le_of_lt_pow
  have h1 : a < 4 ^ a := Nat.lt_pow_self (by norm_num)
  rw [pow_add, show (4 : ℕ) ^ 2 = 16 by norm_num]
  omega

/-- **Size is bounded by the Gödel code**: `tokenSize φ ≤ Encodable.encode φ`. (Foundation's
`toNat` pairs the codes of the immediate subformulas, and `Nat.pair a b ≥ a + b`.)
Source: mandate D3 (`tokenSize_le_of_decode`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem tokenSize_le_encode (φ : Sentence) : tokenSize φ ≤ Encodable.encode φ := by
  rw [encode_sentence_eq_toNat]
  induction φ with
  | atom a =>
      rw [tokenSize_atom]
      show _ ≤ Nat.pair 1 (Encodable.encode a) + 1
      have := length_natDigits4_add_five a
      have := add_two_le_pair_one a
      simp only [Encodable.encode_nat]
      omega
  | falsum =>
      show tokenSize (⊥ : Sentence) ≤ Nat.pair 0 0 + 1
      rw [tokenSize_falsum]
      omega
  | and φ ψ ihφ ihψ =>
      rw [show (Formula.and φ ψ : Sentence) = φ ⋏ ψ from rfl, tokenSize_and]
      show _ ≤ Nat.pair 3 (Nat.pair φ.toNat ψ.toNat) + 1
      have h1 := add_le_pair φ.toNat ψ.toNat
      have h2 := add_le_pair 3 (Nat.pair φ.toNat ψ.toNat)
      omega
  | or φ ψ ihφ ihψ =>
      rw [show (Formula.or φ ψ : Sentence) = φ ⋎ ψ from rfl, tokenSize_or]
      show _ ≤ Nat.pair 4 (Nat.pair φ.toNat ψ.toNat) + 1
      have h1 := add_le_pair φ.toNat ψ.toNat
      have h2 := add_le_pair 4 (Nat.pair φ.toNat ψ.toNat)
      omega
  | imp φ ψ ihφ ihψ =>
      rw [show (Formula.imp φ ψ : Sentence) = φ 🡒 ψ from rfl, tokenSize_imp]
      show _ ≤ Nat.pair 2 (Nat.pair φ.toNat ψ.toNat) + 1
      have h1 := add_le_pair φ.toNat ψ.toNat
      have h2 := add_le_pair 2 (Nat.pair φ.toNat ψ.toNat)
      omega

/-- `Nat.pair` is monotone in each argument.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pair_le_pair {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') : Nat.pair a b ≤ Nat.pair a' b' := by
  calc Nat.pair a b ≤ Nat.pair a' b := by
        rcases ha.lt_or_eq with h | rfl
        · exact (Nat.pair_lt_pair_left b h).le
        · exact le_rfl
    _ ≤ Nat.pair a' b' := by
        rcases hb.lt_or_eq with h | rfl
        · exact (Nat.pair_lt_pair_right a' h).le
        · exact le_rfl

/-- **Decoding does not enlarge the code**: `Formula.ofNat n = some φ → φ.toNat ≤ n`
(`ofNat` is not injective — `ofNat (Nat.pair 0 c + 1) = some ⊥` for every `c` — but a decoded
sentence never has a code above the one it was decoded from).
Source: mandate D3 (`tokenSize_le_of_decode`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem toNat_le_of_ofNat : ∀ (n : ℕ) {φ : Formula ℕ}, Formula.ofNat n = some φ → φ.toNat ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro φ h
      cases n with
      | zero => simp [Formula.ofNat] at h
      | succ e =>
          have hle1 : e.unpair.2.unpair.1 < e + 1 :=
            Nat.lt_succ_iff.mpr (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _))
          have hle2 : e.unpair.2.unpair.2 < e + 1 :=
            Nat.lt_succ_iff.mpr (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _))
          have hpair : Nat.pair e.unpair.1 e.unpair.2 = e := Nat.pair_unpair e
          -- binary-connective case, shared by `🡒`, `⋏`, `⋎`
          have hbin : ∀ (tag : ℕ) (mk : Formula ℕ → Formula ℕ → Formula ℕ),
              (∀ φ ψ, (mk φ ψ).toNat = Nat.pair tag (Nat.pair φ.toNat ψ.toNat) + 1) →
              e.unpair.1 = tag →
              (do
                let φ ← Formula.ofNat e.unpair.2.unpair.1
                let ψ ← Formula.ofNat e.unpair.2.unpair.2
                return mk φ ψ) = some φ → φ.toNat ≤ e + 1 := by
            intro tag mk hmk htag hdo
            change (Formula.ofNat e.unpair.2.unpair.1).bind (fun φ =>
              (Formula.ofNat e.unpair.2.unpair.2).bind (fun ψ => some (mk φ ψ))) = some φ at hdo
            simp only [Option.bind_eq_some_iff, Option.some.injEq] at hdo
            obtain ⟨φ₁, h₁, ψ₁, h₂, rfl⟩ := hdo
            rw [hmk]
            have i1 := ih _ hle1 h₁
            have i2 := ih _ hle2 h₂
            have : Nat.pair tag (Nat.pair φ₁.toNat ψ₁.toNat) ≤ Nat.pair e.unpair.1 e.unpair.2 :=
              pair_le_pair (by omega)
                (le_trans (pair_le_pair i1 i2) (by rw [Nat.pair_unpair]))
            omega
          rw [Formula.ofNat] at h
          simp only at h
          split at h
          · -- `⊥`
            rw [Option.some.injEq] at h
            subst h
            show Nat.pair 0 0 + 1 ≤ e + 1
            simp [Nat.pair]
          · -- atom
            rename_i htag
            simp only [Option.map_eq_some_iff] at h
            obtain ⟨a, ha, rfl⟩ := h
            have ha' : e.unpair.2 = a := by simpa using ha
            subst ha'
            show Nat.pair 1 (Encodable.encode e.unpair.2) + 1 ≤ e + 1
            simp only [Encodable.encode_nat]
            rw [← htag, hpair]
          · rename_i htag
            exact hbin 2 (fun φ ψ => φ 🡒 ψ) (fun _ _ => rfl) htag h
          · rename_i htag
            exact hbin 3 (fun φ ψ => φ ⋏ ψ) (fun _ _ => rfl) htag h
          · rename_i htag
            exact hbin 4 (fun φ ψ => φ ⋎ ψ) (fun _ _ => rfl) htag h
          · simp at h

/-- A decoded token bounds the code of what it decodes to.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma encode_le_of_decode {c : ℕ} {φ : Sentence} (h : Encodable.decode c = some φ) :
    Encodable.encode φ ≤ c := by
  rw [encode_sentence_eq_toNat]
  exact toNat_le_of_ofNat c (by rw [← decode_sentence_eq_ofNat]; exact h)

/-- **The Gödel-escape bound**: a sentence decoded from the token `c` has size at most `c`,
hence below `4 ^ (number of base-4 digits of c)`. (The mandate asks for a bound linear in the
digit count of `c`; that is true but unnecessary — the doubly exponential `sizeBound` absorbs
`4 ^ digits`, which is what the bridge lemma uses.)
Source: mandate D3
Kind: P
Fidelity: weaker: exponential (not linear) in the digit count of `c`, which suffices
Hyps: (a) -/
theorem tokenSize_le_of_decode {c : ℕ} {φ : Sentence} (h : Encodable.decode c = some φ) :
    tokenSize φ ≤ c :=
  le_trans (tokenSize_le_encode φ) (encode_le_of_decode h)

/-- `tokenSize_lt_pow_of_decode`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tokenSize_lt_pow_of_decode {c : ℕ} {φ : Sentence} (h : Encodable.decode c = some φ) :
    tokenSize φ < 4 ^ (natDigits4 c).length :=
  lt_of_le_of_lt (tokenSize_le_of_decode h) (lt_pow_length_natDigits4 c)


/-! ## The contraction lemma: where the tokens of `unRpn ts` come from -/

/-- A successful parse leaves a suffix of its input (from FAF's `parseRpn_strip`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma parseRpn_suffix {fuel : ℕ} {ts : List ℕ} {φ : Sentence} {rest : List ℕ}
    (h : parseRpn fuel ts = some (φ, rest)) : rest <:+ ts := by
  obtain ⟨blk, hblk, -⟩ := parseRpn_strip fuel ts h
  exact ⟨blk, hblk.symm⟩

/-- The three sources of a token of the contracted stream.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def UnRpnSource (ts : List ℕ) (c : ℕ) : Prop :=
  c ∈ ts ∨ c = 0 ∨
    ∃ (rest : List ℕ) (φ : Sentence) (r1 : List ℕ), rest <:+ ts ∧
      parseRpn rest.length rest = some (φ, r1) ∧ c = Encodable.encode φ

/-- `UnRpnSource.mono`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma UnRpnSource.mono {ts ts' : List ℕ} (h : ts <:+ ts') {c : ℕ} (hc : UnRpnSource ts c) :
    UnRpnSource ts' c := by
  rcases hc with hc | hc | ⟨rest, φ, r1, hrest, hp, rfl⟩
  · exact Or.inl (h.subset hc)
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr ⟨rest, φ, r1, hrest.trans h, hp, rfl⟩)

/-- `UnRpnSource.of_mem`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma UnRpnSource.of_mem {ts : List ℕ} {c : ℕ} (h : c ∈ ts) : UnRpnSource ts c := Or.inl h

/-- `UnRpnSource.of_parse`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma UnRpnSource.of_parse {ts : List ℕ} {φ : Sentence} {r1 : List ℕ}
    (hp : parseRpn ts.length ts = some (φ, r1)) : UnRpnSource ts (Encodable.encode φ) :=
  Or.inr (Or.inr ⟨ts, φ, r1, List.suffix_refl ts, hp, rfl⟩)

/-- **Contraction lemma.** Every token of `unRpnTokens fuel ts` is a token of `ts`, or the
failure marker `0`, or the Gödel code of a sentence `parseRpn` reads from a suffix of `ts`.
Source: mandate T1 (extraction step)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem mem_unRpnTokens : ∀ (fuel : ℕ) (ts : List ℕ) {c : ℕ}, c ∈ unRpnTokens fuel ts →
    UnRpnSource ts c := by
  intro fuel
  induction fuel with
  | zero =>
      intro ts c hc
      cases ts <;> simp [unRpnTokens] at hc
  | succ fuel ih =>
      intro ts c hc
      cases ts with
      | nil => simp [unRpnTokens] at hc
      | cons t rest =>
          rw [unRpnTokens_cons] at hc
          have hrest : rest <:+ t :: rest := List.suffix_cons t rest
          by_cases h0 : t = 0
          · rw [if_pos h0] at hc
            subst h0
            rcases hp : parseRpn rest.length rest with _ | ⟨φ, r1⟩
            · rw [hp] at hc
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
              rcases hc with rfl | rfl <;> exact Or.inr (Or.inl rfl)
            · rw [hp] at hc
              rcases r1 with _ | ⟨d, r2⟩
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
                rcases hc with rfl | rfl
                · exact Or.inl (List.mem_cons_self)
                · exact (UnRpnSource.of_parse hp).mono hrest
              · simp only [List.mem_cons] at hc
                rcases hc with rfl | rfl | rfl | hc
                · exact Or.inl (List.mem_cons_self)
                · exact (UnRpnSource.of_parse hp).mono hrest
                · exact Or.inl ((parseRpn_suffix hp).subset List.mem_cons_self |> hrest.subset)
                · exact (ih r2 hc).mono ((List.suffix_cons d r2).trans ((parseRpn_suffix hp).trans hrest))
          rw [if_neg h0] at hc
          by_cases h6 : t = 6
          · rw [if_pos h6] at hc
            subst h6
            rcases hp : parseRpn rest.length rest with _ | ⟨φ, r1⟩
            · rw [hp] at hc
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
              rcases hc with rfl | rfl
              · exact Or.inl (List.mem_cons_self)
              · exact Or.inr (Or.inl rfl)
            · rw [hp] at hc
              simp only [List.mem_cons] at hc
              rcases hc with rfl | rfl | hc
              · exact Or.inl (List.mem_cons_self)
              · exact (UnRpnSource.of_parse hp).mono hrest
              · exact (ih r1 hc).mono ((parseRpn_suffix hp).trans hrest)
          rw [if_neg h6] at hc
          -- the two payload tags copy one token
          have hpayload : ∀ (u : ℕ), u = t → ∀ (hc' : c ∈ (match rest with
              | [] => [u]
              | c' :: r => u :: c' :: unRpnTokens fuel r)), UnRpnSource (t :: rest) c := by
            intro u hu hc'
            subst hu
            rcases rest with _ | ⟨c', r⟩
            · simp only [List.mem_singleton] at hc'
              subst hc'
              exact Or.inl List.mem_cons_self
            · simp only [List.mem_cons] at hc'
              rcases hc' with rfl | rfl | hc'
              · exact Or.inl List.mem_cons_self
              · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
              · exact (ih r hc').mono ((List.suffix_cons c' r).trans hrest)
          by_cases h1 : t = 1
          · rw [if_pos h1] at hc
            exact hpayload 1 h1.symm hc
          rw [if_neg h1] at hc
          by_cases h7 : t = 7
          · rw [if_pos h7] at hc
            exact hpayload 7 h7.symm hc
          rw [if_neg h7] at hc
          simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact Or.inl List.mem_cons_self
          · exact (ih rest hc).mono hrest

/-- `mem_unRpn`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_unRpn {ts : List ℕ} {c : ℕ} (hc : c ∈ unRpn ts) : UnRpnSource ts c :=
  mem_unRpnTokens ts.length ts hc

/-! ## The digit layer: tokens of `undigitize ds` are short -/

/-- The fold invariant of `undigitize`: after `k` digits, every finished token is `< 4 ^ k`, the
accumulator is below its place value, the place value is `≤ 4 ^ k`, and at most `k` tokens have
been finished.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma undigitize_fold_invariant (ds : List ℕ) :
    ∀ (out : List ℕ) (acc pow k : ℕ), (∀ t ∈ out, t < 4 ^ k) → acc < pow → pow ≤ 4 ^ k →
      out.length ≤ k →
      let st := ds.foldl undigitizeStep (out, acc, pow)
      (∀ t ∈ st.1, t < 4 ^ (k + ds.length)) ∧ st.2.1 < st.2.2 ∧ st.2.2 ≤ 4 ^ (k + ds.length) ∧
        st.1.length ≤ k + ds.length := by
  induction ds with
  | nil =>
      intro out acc pow k hout hacc hpow hlen
      simpa using ⟨hout, hacc, hpow, hlen⟩
  | cons d ds ih =>
      intro out acc pow k hout hacc hpow hlen
      simp only [List.foldl_cons, List.length_cons]
      have hstep : undigitizeStep (out, acc, pow) d =
          if d < 4 then (out, acc + d * pow, 4 * pow) else (out ++ [acc], 0, 1) := rfl
      rw [hstep]
      have h4k : 4 ^ k ≤ 4 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      split_ifs with hd
      · have := ih out (acc + d * pow) (4 * pow) (k + 1)
          (fun t ht => lt_of_lt_of_le (hout t ht) h4k) (by nlinarith)
          (by rw [pow_succ]; omega) (by omega)
        simpa [Nat.add_right_comm k 1 ds.length, Nat.add_assoc] using this
      · have := ih (out ++ [acc]) 0 1 (k + 1)
          (fun t ht => by
            rw [List.mem_append, List.mem_singleton] at ht
            rcases ht with ht | rfl
            · exact lt_of_lt_of_le (hout t ht) h4k
            · exact lt_of_lt_of_le hacc (le_trans hpow h4k))
          (by norm_num) (Nat.one_le_pow _ _ (by norm_num)) (by simp; omega)
        simpa [Nat.add_right_comm k 1 ds.length, Nat.add_assoc] using this

/-- Every token of `undigitize ds` is below `4 ^ ds.length`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lt_pow_length_of_mem_undigitize {ds : List ℕ} {t : ℕ} (ht : t ∈ undigitize ds) :
    t < 4 ^ ds.length := by
  have := (undigitize_fold_invariant ds [] 0 1 0 (by simp) (by norm_num) (by norm_num) (by simp)).1
  unfold undigitize at ht
  simpa using this t ht

/-- `undigitize ds` has at most `ds.length` tokens.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma length_undigitize_le (ds : List ℕ) : (undigitize ds).length ≤ ds.length := by
  have := (undigitize_fold_invariant ds [] 0 1 0 (by simp) (by norm_num) (by norm_num) (by simp)).2.2.2
  unfold undigitize
  simpa using this

/-! ## The stream lemma: the decoder produces sentences only by decoding a token -/

/-- Every sentence held in a decoder state came from decoding a token of `us`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def StreamInv (us : List ℕ) : Option EF.StreamState → Prop
  | none => True
  | some ((_, pending), (efst, trades)) =>
      (∀ φ, pending = some φ → ∃ c ∈ us, Encodable.decode c = some φ) ∧
      (∀ e ∈ efst, ∀ k φ, (k, φ) ∈ e.priceQueries → ∃ c ∈ us, Encodable.decode c = some φ) ∧
      (∀ p ∈ trades, (∃ c ∈ us, Encodable.decode c = some p.2) ∧
        ∀ k φ, (k, φ) ∈ p.1.priceQueries → ∃ c ∈ us, Encodable.decode c = some φ)

/-- `streamInv_initial`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma streamInv_initial (us : List ℕ) : StreamInv us (some EF.streamInitial) := by
  simp [StreamInv, EF.streamInitial]

/-- One decoder step preserves the invariant, provided the consumed token is in `us`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma streamInv_step (us : List ℕ) (st : Option EF.StreamState) {t : ℕ} (ht : t ∈ us)
    (hst : StreamInv us st) : StreamInv us (EF.streamStep st t) := by
  rcases st with _ | ⟨⟨mode, pending⟩, efst, trades⟩
  · trivial
  obtain ⟨hpend, hstack, htrades⟩ := hst
  -- helper: pushing a feature whose queries are covered keeps the stack covered
  have hpush : ∀ (e : EF) (rest : List EF),
      (∀ k φ, (k, φ) ∈ e.priceQueries → ∃ c ∈ us, Encodable.decode c = some φ) →
      (∀ e' ∈ rest, ∀ k φ, (k, φ) ∈ e'.priceQueries → ∃ c ∈ us, Encodable.decode c = some φ) →
      ∀ e' ∈ e :: rest, ∀ k φ, (k, φ) ∈ e'.priceQueries → ∃ c ∈ us, Encodable.decode c = some φ := by
    intro e rest he hrest e' he'
    rw [List.mem_cons] at he'
    rcases he' with rfl | he'
    · exact he
    · exact hrest e' he'
  have hpop : ∀ (e : EF) (rest : List EF),
      (∀ e' ∈ e :: rest, ∀ k φ, (k, φ) ∈ e'.priceQueries → ∃ c ∈ us, Encodable.decode c = some φ) →
      (∀ k φ, (k, φ) ∈ e.priceQueries → ∃ c ∈ us, Encodable.decode c = some φ) ∧
      ∀ e' ∈ rest, ∀ k φ, (k, φ) ∈ e'.priceQueries → ∃ c ∈ us, Encodable.decode c = some φ :=
    fun e rest h => ⟨h e List.mem_cons_self, fun e' he' => h e' (List.mem_cons_of_mem _ he')⟩
  simp only [EF.streamStep]
  split_ifs with hm0 ht0 ht1 ht2 ht3 ht4 ht5 ht6 ht7 ht8 hm1 hm2 hm3 hm4 hm5
  · exact ⟨by simp, hstack, htrades⟩
  · exact ⟨by simp, hstack, htrades⟩
  · -- add
    rcases efst with _ | ⟨b, _ | ⟨a, rest⟩⟩ <;> try trivial
    obtain ⟨hb, h⟩ := hpop _ _ hstack
    obtain ⟨ha, hrest⟩ := hpop _ _ h
    refine ⟨by simp, hpush _ _ ?_ hrest, htrades⟩
    intro k φ hk
    simp only [EF.priceQueries, List.mem_append] at hk
    exact hk.elim (ha k φ) (hb k φ)
  · -- mul
    rcases efst with _ | ⟨b, _ | ⟨a, rest⟩⟩ <;> try trivial
    obtain ⟨hb, h⟩ := hpop _ _ hstack
    obtain ⟨ha, hrest⟩ := hpop _ _ h
    refine ⟨by simp, hpush _ _ ?_ hrest, htrades⟩
    intro k φ hk
    simp only [EF.priceQueries, List.mem_append] at hk
    exact hk.elim (ha k φ) (hb k φ)
  · -- max
    rcases efst with _ | ⟨b, _ | ⟨a, rest⟩⟩ <;> try trivial
    obtain ⟨hb, h⟩ := hpop _ _ hstack
    obtain ⟨ha, hrest⟩ := hpop _ _ h
    refine ⟨by simp, hpush _ _ ?_ hrest, htrades⟩
    intro k φ hk
    simp only [EF.priceQueries, List.mem_append] at hk
    exact hk.elim (ha k φ) (hb k φ)
  · -- safeRecip
    rcases efst with _ | ⟨a, rest⟩ <;> try trivial
    obtain ⟨ha, hrest⟩ := hpop _ _ hstack
    refine ⟨by simp, hpush _ _ ?_ hrest, htrades⟩
    intro k φ hk
    simp only [EF.priceQueries] at hk
    exact ha k φ hk
  · exact ⟨by simp, hstack, htrades⟩
  · exact ⟨by simp, hstack, htrades⟩
  · -- letE
    rcases efst with _ | ⟨body, _ | ⟨x, rest⟩⟩ <;> try trivial
    obtain ⟨hbody, h⟩ := hpop _ _ hstack
    obtain ⟨hx, hrest⟩ := hpop _ _ h
    refine ⟨by simp, hpush _ _ ?_ hrest, htrades⟩
    intro k φ hk
    simp only [EF.priceQueries, List.mem_append] at hk
    exact hk.elim (hx k φ) (hbody k φ)
  · trivial
  · -- mode 1: decode a price sentence
    rcases hdec : Encodable.decode (α := Sentence) t with _ | φ
    · trivial
    · refine ⟨?_, hstack, htrades⟩
      intro ψ hψ
      rw [Option.some.injEq] at hψ
      subst hψ
      exact ⟨t, ht, hdec⟩
  · -- mode 2: the day token closes a price leaf
    rcases hp : pending with _ | φ
    · trivial
    · refine ⟨by simp, hpush _ _ ?_ hstack, htrades⟩
      intro k ψ hk
      simp only [EF.priceQueries, List.mem_singleton, Prod.mk.injEq] at hk
      obtain ⟨-, hψ⟩ := hk
      rw [hψ]
      exact hpend φ hp
  · -- mode 3: a rational constant
    rcases Encodable.decode (α := ℚ) t with _ | q
    · trivial
    · refine ⟨by simp, hpush _ _ ?_ hstack, htrades⟩
      intro k ψ hk
      simp [EF.priceQueries] at hk
  · -- mode 4: record a trade
    rcases efst with _ | ⟨e, rest⟩
    · rcases Encodable.decode (α := Sentence) t with _ | φ <;> trivial
    · rcases hdec : Encodable.decode (α := Sentence) t with _ | φ
      · trivial
      · obtain ⟨he, hrest⟩ := hpop _ _ hstack
        refine ⟨by simp, hrest, ?_⟩
        intro p hp
        rw [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact htrades p hp
        · exact ⟨⟨t, ht, hdec⟩, he⟩
  · -- mode 5: a variable
    refine ⟨by simp, hpush _ _ ?_ hstack, htrades⟩
    intro k ψ hk
    simp [EF.priceQueries] at hk
  · trivial

/-- `streamInv_foldl`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma streamInv_foldl (us : List ℕ) : ∀ (l : List ℕ) (st : Option EF.StreamState),
    (∀ t ∈ l, t ∈ us) → StreamInv us st → StreamInv us (l.foldl EF.streamStep st) := by
  intro l
  induction l with
  | nil => intro st _ h; simpa using h
  | cons t l ih =>
      intro st hl hst
      rw [List.foldl_cons]
      exact ih _ (fun t' ht' => hl t' (List.mem_cons_of_mem _ ht'))
        (streamInv_step us st (hl t List.mem_cons_self) hst)

/-- **Stream lemma.** Every sentence mentioned by `strategyOfTokens n us` is the decoding of a
token of `us`.
Source: mandate T1 (extraction step)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem exists_token_of_mentionedBy {n : ℕ} {us : List ℕ} {φ : Sentence}
    (h : MentionedBy (strategyOfTokens n us) φ) : ∃ c ∈ us, Encodable.decode c = some φ := by
  -- the trades of the decoded strategy are those of `deserializeTrades us` (or none)
  have htr : ∀ p ∈ (strategyOfTokens n us).trades, ∃ trades, deserializeTrades us = some trades ∧
      p ∈ trades := by
    intro p hp
    unfold strategyOfTokens at hp
    split at hp
    · simp at hp
    · rename_i trades hdecode
      split at hp
      · exact ⟨trades, hdecode, hp⟩
      · simp at hp
  have hinv : ∀ trades, deserializeTrades us = some trades →
      ∀ p ∈ trades, (∃ c ∈ us, Encodable.decode c = some p.2) ∧
        ∀ k ψ, (k, ψ) ∈ p.1.priceQueries → ∃ c ∈ us, Encodable.decode c = some ψ := by
    intro trades hdes
    unfold deserializeTrades at hdes
    have hfold := streamInv_foldl us us (some EF.streamInitial) (fun _ h => h)
      (streamInv_initial us)
    unfold EF.streamReadFrom at hdes
    split at hdes
    · rename_i st hst
      rw [hst] at hfold
      rw [Option.some.injEq] at hdes
      subst hdes
      exact hfold.2.2
    · simp at hdes
  rcases h with ⟨e, he⟩ | ⟨p, hp, k, hk⟩
  · obtain ⟨trades, hdes, hmem⟩ := htr _ he
    exact (hinv trades hdes _ hmem).1
  · obtain ⟨trades, hdes, hmem⟩ := htr _ hp
    exact (hinv trades hdes _ hmem).2 k φ hk


/-! ## The parse-size lemma

The structured-escape bound `tokenSize_le_of_structured` it consumes is `Structured.lean`'s. -/

/-- **Parse-size lemma**, parametric in a monotone bound `S` on the structured escape: a sentence
`parseRpn` reads by consuming `L` tokens all below `M` has size at most `L · (M + S L + 3)` — the
canonical spelling contributes one block per token, the Gödel escape `1 :: c` contributes
`c < M`, the structured escape contributes `S`, and the connectives add `≤ 3`.
Source: mandate T1 (parse-size step)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem tokenSize_le_of_parseRpn (S : ℕ → ℕ) (hSmono : Monotone S)
    (hS : ∀ (ts : List ℕ) (φ : Sentence) (rest : List ℕ),
      parseStructuredPaperPrime ts = some (φ, rest) → tokenSize φ ≤ S (ts.length - rest.length)) :
    ∀ (fuel : ℕ) (ts : List ℕ) {φ : Sentence} {rest : List ℕ} {M : ℕ},
      parseRpn fuel ts = some (φ, rest) → (∀ t ∈ ts, t < M) →
        tokenSize φ ≤ (ts.length - rest.length) * (M + S (ts.length - rest.length) + 3) := by
  intro fuel
  induction fuel with
  | zero => intro ts φ rest M h; simp [parseRpn] at h
  | succ fuel ih =>
      intro ts φ rest M h hM
      rcases ts with _ | ⟨t, ts'⟩
      · simp [parseRpn] at h
      rw [parseRpn_cons] at h
      by_cases h0 : t = 0
      · rw [if_pos h0] at h
        have := Option.some.inj h
        rw [Prod.mk.injEq] at this
        obtain ⟨hφ, hr⟩ := this
        subst hφ; subst hr
        show tokenSize (⊥ : Sentence) ≤ _
        rw [tokenSize_falsum]
        have hL : (t :: ts').length - ts'.length = 1 := by simp
        rw [hL]
        omega
      rw [if_neg h0] at h
      by_cases h1 : t = 1
      · rw [if_pos h1] at h
        rcases ts' with _ | ⟨c, tail⟩
        · simp at h
        cases c with
        | zero =>
            have hst := hS tail φ rest h
            have hlen := (parseStructuredPaperPrime_suffix h).length_le
            have hL : (t :: 0 :: tail).length - rest.length = tail.length - rest.length + 2 := by
              simp only [List.length_cons]; omega
            rw [hL]
            have hmono := hSmono (show tail.length - rest.length ≤ tail.length - rest.length + 2 by omega)
            have hpos : 1 ≤ tail.length - rest.length + 2 := by omega
            calc tokenSize φ ≤ S (tail.length - rest.length) := hst
              _ ≤ S (tail.length - rest.length + 2) := hmono
              _ ≤ 1 * (M + S (tail.length - rest.length + 2) + 3) := by omega
              _ ≤ (tail.length - rest.length + 2) * (M + S (tail.length - rest.length + 2) + 3) :=
                  Nat.mul_le_mul_right _ hpos
        | succ c =>
            rcases hdec : Encodable.decode (α := Sentence) (c + 1) with _ | ψ
            · simp [hdec] at h
            · simp only [hdec, Option.map_some] at h
              have := Option.some.inj h
              rw [Prod.mk.injEq] at this
              obtain ⟨hφ, hr⟩ := this
              subst hφ; subst hr
              have hc : c + 1 < M := hM (c + 1) (List.mem_cons_of_mem _ List.mem_cons_self)
              have hts := tokenSize_le_of_decode hdec
              have hL : (t :: (c + 1) :: tail).length - tail.length = 2 := by
                simp only [List.length_cons]; omega
              rw [hL]
              omega
      rw [if_neg h1] at h
      -- the three binary connectives
      have hbin : ∀ (mk : Sentence → Sentence → Sentence) (k : ℕ),
          (∀ a b, tokenSize (mk a b) ≤ k + tokenSize a + tokenSize b) → k ≤ 3 →
          (parseRpn fuel ts').bind
            (fun p => (parseRpn fuel p.2).bind fun q => some (mk p.1 q.1, q.2)) = some (φ, rest) →
          tokenSize φ ≤ ((t :: ts').length - rest.length) *
            (M + S ((t :: ts').length - rest.length) + 3) := by
        intro mk k hmk hk hb
        rcases hp1 : parseRpn fuel ts' with _ | ⟨φ1, r1⟩
        · rw [hp1] at hb; simp at hb
        rcases hp2 : parseRpn fuel r1 with _ | ⟨φ2, r2⟩
        · rw [hp1] at hb; simp only [Option.bind_some] at hb; rw [hp2] at hb; simp at hb
        rw [hp1] at hb
        simp only [Option.bind_some] at hb
        rw [hp2] at hb
        simp only [Option.bind_some] at hb
        have := Option.some.inj hb
        rw [Prod.mk.injEq] at this
        obtain ⟨hφ, hr⟩ := this
        subst hφ; subst hr
        have l1 := parseRpn_length_lt fuel ts' φ1 r1 hp1
        have l2 := parseRpn_length_lt fuel r1 φ2 r2 hp2
        have hM' : ∀ x ∈ ts', x < M := fun x hx => hM x (List.mem_cons_of_mem _ hx)
        have hM'' : ∀ x ∈ r1, x < M :=
          fun x hx => hM' x ((parseRpn_suffix hp1).subset hx)
        have i1 := ih ts' hp1 hM'
        have i2 := ih r1 hp2 hM''
        have hL : (t :: ts').length - r2.length =
            (ts'.length - r1.length) + (r1.length - r2.length) + 1 := by
          simp only [List.length_cons]; omega
        rw [hL]
        set L1 := ts'.length - r1.length with hL1
        set L2 := r1.length - r2.length with hL2
        have hm1 := hSmono (show L1 ≤ L1 + L2 + 1 by omega)
        have hm2 := hSmono (show L2 ≤ L1 + L2 + 1 by omega)
        have hstep1 : L1 * (M + S L1 + 3) ≤ L1 * (M + S (L1 + L2 + 1) + 3) :=
          Nat.mul_le_mul_left _ (by omega)
        have hstep2 : L2 * (M + S L2 + 3) ≤ L2 * (M + S (L1 + L2 + 1) + 3) :=
          Nat.mul_le_mul_left _ (by omega)
        have hsum : (L1 + L2 + 1) * (M + S (L1 + L2 + 1) + 3) =
            L1 * (M + S (L1 + L2 + 1) + 3) + L2 * (M + S (L1 + L2 + 1) + 3) +
              (M + S (L1 + L2 + 1) + 3) := by ring
        have := hmk φ1 φ2
        omega
      by_cases h2 : t = 2
      · rw [if_pos h2] at h
        exact hbin (fun a b => Formula.imp a b) 2
          (fun a b => by rw [show (Formula.imp a b : Sentence) = a 🡒 b from rfl, tokenSize_imp])
          (by norm_num) h
      rw [if_neg h2] at h
      by_cases h3 : t = 3
      · rw [if_pos h3] at h
        exact hbin (fun a b => Formula.and a b) 2
          (fun a b => by rw [show (Formula.and a b : Sentence) = a ⋏ b from rfl, tokenSize_and])
          (by norm_num) h
      rw [if_neg h3] at h
      by_cases h4 : t = 4
      · rw [if_pos h4] at h
        exact hbin (fun a b => Formula.or a b) 3
          (fun a b => by rw [show (Formula.or a b : Sentence) = a ⋎ b from rfl, tokenSize_or])
          (by norm_num) h
      rw [if_neg h4] at h
      -- canonical atom
      have := Option.some.inj h
      rw [Prod.mk.injEq] at this
      obtain ⟨hφ, hr⟩ := this
      subst hφ; subst hr
      have ht5 : t - 5 + 5 = t := by omega
      rw [tokenSize_atom, ht5]
      have hd := length_natDigits4_le_succ t
      have htM := hM t List.mem_cons_self
      have hL : (t :: ts').length - ts'.length = 1 := by simp
      rw [hL]
      omega

/-! ## Arithmetic: polynomials and the doubly exponential bound -/

/-- A natural polynomial is bounded by (sum of coefficients) · `(n + 1) ^ natDegree`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma polynomial_eval_le (p : Polynomial ℕ) (n : ℕ) :
    p.eval n ≤ (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) * (n + 1) ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mem_range] at hi
  apply Nat.mul_le_mul_left
  calc n ^ i ≤ (n + 1) ^ i := Nat.pow_le_pow_left (Nat.le_succ n) i
    _ ≤ (n + 1) ^ p.natDegree := Nat.pow_le_pow_right (by omega) (by omega)

/-- `k ^ 2 ≤ 2 ^ k` for `k ≥ 4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sq_le_two_pow {k : ℕ} (hk : 4 ≤ k) : k ^ 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      rw [pow_succ 2 k]
      have h1 : 2 * k + 1 ≤ k ^ 2 := by nlinarith
      nlinarith

/-- **Growth**: `A · (n + 1) ^ E ≤ 2 ^ n` from `n ≥ 2 ^ (A + 3E + 4)` on (through
`n^E ≤ 2^{E (log₂ n + 1)}` and `(log₂ n)² ≤ 2^{log₂ n} ≤ n`).
Source: mandate T1 (arithmetic step)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem eventually_poly_le_two_pow (A E : ℕ) :
    ∃ N, ∀ n ≥ N, A * (n + 1) ^ E ≤ 2 ^ n := by
  refine ⟨2 ^ (A + 3 * E + 4), fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by
    have : 1 ≤ 2 ^ (A + 3 * E + 4) := Nat.one_le_two_pow
    omega
  set l := Nat.log 2 n with hl
  have hl_ge : A + 3 * E + 4 ≤ l := Nat.le_log_of_pow_le (by norm_num) hn
  have hn_lt : n < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hl_le : 2 ^ l ≤ n := Nat.pow_log_le_self 2 hn0
  have h1 : (n + 1) ^ E ≤ 2 ^ (E * (l + 1)) := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left (by omega) E
  have hA : A ≤ 2 ^ A := Nat.lt_two_pow_self.le
  have h2 : A * (n + 1) ^ E ≤ 2 ^ (A + E * (l + 1)) := by
    rw [pow_add]
    exact Nat.mul_le_mul hA h1
  have h3 : A + E * (l + 1) ≤ l ^ 2 := by nlinarith
  have h4 : l ^ 2 ≤ 2 ^ l := sq_le_two_pow (by omega)
  calc A * (n + 1) ^ E ≤ 2 ^ (A + E * (l + 1)) := h2
    _ ≤ 2 ^ (l ^ 2) := Nat.pow_le_pow_right (by norm_num) h3
    _ ≤ 2 ^ (2 ^ l) := Nat.pow_le_pow_right (by norm_num) h4
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hl_le

/-- The size bound of everything a machine word of `P` digits can name (with the structured
constant `C`): `P · (4^P + 2^{C P} + C + 3)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def bridgeBound (C P : ℕ) : ℕ := P * (4 ^ P + (2 ^ (C * P) + C) + 3)

/-- `bridgeBound_mono`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma bridgeBound_mono (C : ℕ) {P P' : ℕ} (h : P ≤ P') : bridgeBound C P ≤ bridgeBound C P' := by
  unfold bridgeBound
  apply Nat.mul_le_mul h
  have h4 := Nat.pow_le_pow_right (show 0 < 4 by norm_num) h
  have h2 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Nat.mul_le_mul_left C h)
  exact Nat.add_le_add_right (Nat.add_le_add h4 (Nat.add_le_add_right h2 C)) 3

/-- `bridgeBound_le`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma bridgeBound_le (C P : ℕ) : bridgeBound C P ≤ 2 ^ ((C + 6) * (P + 1)) := by
  rcases Nat.eq_zero_or_pos P with rfl | hP
  · simp [bridgeBound]
  have hP1 : P ≤ 2 ^ P := Nat.lt_two_pow_self.le
  have h4 : 4 ^ P ≤ 2 ^ ((C + 5) * P) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hC : 2 ^ (C * P) ≤ 2 ^ ((C + 5) * P) :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hc3 : C + 3 ≤ 2 ^ ((C + 5) * P) := by
    calc C + 3 ≤ 2 ^ (C + 3) := Nat.lt_two_pow_self.le
      _ ≤ 2 ^ ((C + 5) * P) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hsum : 4 ^ P + (2 ^ (C * P) + C) + 3 ≤ 4 * 2 ^ ((C + 5) * P) := by omega
  calc bridgeBound C P = P * (4 ^ P + (2 ^ (C * P) + C) + 3) := rfl
    _ ≤ 2 ^ P * (4 * 2 ^ ((C + 5) * P)) := Nat.mul_le_mul hP1 hsum
    _ = 2 ^ (P + 2 + (C + 5) * P) := by
        rw [pow_add, pow_add]
        ring
    _ ≤ 2 ^ ((C + 6) * (P + 1)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-! ## The bridge lemma -/

/-- Every sentence mentioned by the strategy decoded from a word `w` has size at most
`bridgeBound C (bitsToDigits w).length`, where `C` is the structured-escape constant.
Source: mandate T1
Kind: C
Fidelity: exact
Hyps: (a), given the structured bound as `hC` (proved in `Structured.lean`, `tokenSize_le_of_structured`; it was OPEN in the first pass) -/
theorem tokenSize_le_bridgeBound_of_mentionedBy {C : ℕ}
    (hC : ∀ (ts : List ℕ) (φ : Sentence) (rest : List ℕ),
      parseStructuredPaperPrime ts = some (φ, rest) →
        tokenSize φ ≤ 2 ^ (C * (ts.length - rest.length)) + C)
    {n : ℕ} {w : List Bool} {φ : Sentence} (hφ : MentionedBy (strategyOfOutput n w) φ) :
    tokenSize φ ≤ bridgeBound C (bitsToDigits w).length := by
  set ds := bitsToDigits w with hds
  set ts := undigitize ds with hts
  set P := ds.length with hP
  have hφ' : MentionedBy (strategyOfTokens n (unRpn ts)) φ := hφ
  obtain ⟨c, hc, hdec⟩ := exists_token_of_mentionedBy hφ'
  have hts_len : ts.length ≤ P := length_undigitize_le ds
  have hts_lt : ∀ t ∈ ts, t < 4 ^ P := fun t ht => lt_pow_length_of_mem_undigitize ht
  have hS : Monotone fun L => 2 ^ (C * L) + C := fun a b hab => by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Nat.mul_le_mul_left C hab)
    exact Nat.add_le_add_right this C
  rcases mem_unRpn hc with hmem | hzero | ⟨rest, φ', r1, hrest, hp, rfl⟩
  · -- a copied token: the Gödel-escape bound
    have hP1 : 1 ≤ P := by
      have : ts ≠ [] := List.ne_nil_of_mem hmem
      have : 1 ≤ ts.length := List.length_pos_of_ne_nil this
      omega
    have h1 := tokenSize_le_of_decode hdec
    have h2 := hts_lt c hmem
    unfold bridgeBound
    calc tokenSize φ ≤ 4 ^ P := le_trans h1 h2.le
      _ ≤ 1 * (4 ^ P + (2 ^ (C * P) + C) + 3) := by
          rw [one_mul]
          exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
      _ ≤ P * (4 ^ P + (2 ^ (C * P) + C) + 3) := Nat.mul_le_mul_right _ hP1
  · -- the failure marker decodes to nothing
    subst hzero
    rw [decode_zero_sentence] at hdec
    exact absurd hdec (by simp)
  · -- a contracted block: the parse-size lemma on a suffix of `ts`
    rw [Encodable.encodek, Option.some.injEq] at hdec
    rw [← hdec]
    have hM : ∀ t ∈ rest, t < 4 ^ P := fun t ht => hts_lt t (hrest.subset ht)
    have hbound := tokenSize_le_of_parseRpn (fun L => 2 ^ (C * L) + C) hS hC rest.length rest hp hM
    have hL : rest.length - r1.length ≤ P := le_trans (Nat.sub_le _ _) (le_trans hrest.length_le hts_len)
    have hmono := hS hL
    simp only at hmono
    calc tokenSize φ' ≤ (rest.length - r1.length) *
          (4 ^ P + (2 ^ (C * (rest.length - r1.length)) + C) + 3) := hbound
      _ ≤ P * (4 ^ P + (2 ^ (C * P) + C) + 3) :=
          Nat.mul_le_mul hL (Nat.add_le_add_right (Nat.add_le_add_left hmono _) 3)

/-- **The bridge lemma (F1, T1).** An efficiently computable trader eventually names only
day-small sentences: for `Tr` with `EfficientlyComputable Tr` there is `N` such that for every
`n ≥ N`, every sentence mentioned by `Tr.strat n` — traded or inside a price leaf — is small on
day `n`. Derived from FAF's `def:ec` metering; nothing about traders is assumed. Every input is
proved here or in FAF: the FP output-length polynomial, the digit/token stream bounds, the stream
and contraction lemmas, the parse-size lemma with the Gödel-escape bound and the structured-escape
bound (`Structured.lean`, formerly OPEN), and the growth arithmetic.
Source: bli-paper-031 footnote; bli-slides-030; bli-soto-a-002 (reading A); [[bli-program]] §2.1; mandate T1
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem bridge_lemma (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ∃ N, ∀ n ≥ N, ∀ φ, MentionedBy (Tr.strat n) φ → SmallOn n φ := by
  obtain ⟨C, hC⟩ := tokenSize_le_of_structured
  obtain ⟨F, hF, hstrat⟩ := hTr
  obtain ⟨p, hp⟩ := Complexity.Cobham.output_length_poly_of_mem_FP hF
  set A := ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i with hA
  set E := p.natDegree with hE
  obtain ⟨N, hN⟩ := eventually_poly_le_two_pow ((C + 6) * (A + 1)) E
  refine ⟨N, fun n hn φ hφ => ?_⟩
  rw [← hstrat n] at hφ
  have hsize := tokenSize_le_bridgeBound_of_mentionedBy hC hφ
  have hdig : (bitsToDigits (F (unaryDay n))).length ≤ p.eval n := by
    rw [length_bitsToDigits]
    have := hp (unaryDay n)
    rw [length_unaryDay] at this
    omega
  have hpoly : p.eval n + 1 ≤ (A + 1) * (n + 1) ^ E := by
    have h1 := polynomial_eval_le p n
    have h2 : 1 ≤ (n + 1) ^ E := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hexp : (C + 6) * (p.eval n + 1) ≤ 2 ^ n := by
    calc (C + 6) * (p.eval n + 1) ≤ (C + 6) * ((A + 1) * (n + 1) ^ E) :=
          Nat.mul_le_mul_left _ hpoly
      _ = (C + 6) * (A + 1) * (n + 1) ^ E := by ring
      _ ≤ 2 ^ n := hN n hn
  unfold SmallOn sizeBound
  calc tokenSize φ ≤ bridgeBound C (bitsToDigits (F (unaryDay n))).length := hsize
    _ ≤ bridgeBound C (p.eval n) := bridgeBound_mono C hdig
    _ ≤ 2 ^ ((C + 6) * (p.eval n + 1)) := bridgeBound_le C _
    _ ≤ 2 ^ (2 ^ n) := Nat.pow_le_pow_right (by norm_num) hexp

end Cleanroom.Bli.BliFound
