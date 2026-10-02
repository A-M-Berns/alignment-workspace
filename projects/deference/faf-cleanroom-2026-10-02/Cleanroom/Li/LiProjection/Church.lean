import Cleanroom.Li.LiProjection.Recover
import Cleanroom.Li.LiProjection.Witnesses
import LogicalInduction.Construction.Primcodable
import Foundation.FirstOrder.Incompleteness.Halting

/-!
# `li-projection` · Church: uniform limit non-recoverability with a computable modulus, proved outright (T6.2), and LI Proposition 5.5.1

Package `Cleanroom.Li.LiProjection` ([[li-projection-mandate]]), file 14 of the layout (added in
repair round 1; audit r1 fidelity N3 asked for the Church half of T6.2 to be isolated).

T6.2 says: no computable `f : ℕ → ℕ → ℚ` approximates every limiting belief of an inductor over
`paperDP T` uniformly (`|f ⌜σ⌝ k − P_∞(⌜σ⌝)| ≤ 1/(k+1)`). The LI half — `P_∞ = 1 ↔ T ⊢ σ` for every
inductor over `paperDP T` — is `Recover.lean`'s `limitingBelief_paperPrime_eq_one_iff`. This file
does the recursion-theoretic half **along the halting family**: with `haltCode := codeOfREPred
(fun c => (eval c 0).Dom)` (Foundation's Σ₁ code of Mathlib's halting predicate),

* `halt_iff_provable`: `(eval a 0).Dom ↔ T ⊢ haltSentence a` — Foundation's `re_complete`
  (Σ₁-completeness under `T.SoundOnHierarchy 𝚺 1`);
* `provable_haltCode_re`: `fun a ↦ T ⊢ haltSentence a` is r.e. (it *is* the halting predicate);
* **`church_haltCode`**: it is not computable — Church's theorem along the numeral family, from
  Mathlib's `ComputablePred.halting_problem`; proved outright, no coding of substitution needed;
* `exists_search_iff_lt_one`: the search `∃ k, (k+1)·F k < k` on a uniform approximant `F` of a
  real `L` is equivalent to `L < 1` (pure analysis);
* `search_re`: for a computable `f : ℕ → ℕ → ℚ`, the search `fun c ↦ ∃ k, (k+1)·f c k < k` is r.e.
  *in the sentence code `c`* (`Partrec.rfind` on the search bit);
* **`rePred_comp_numeralSubst`** (repair round 2): r.e. predicates on sentence codes pull back along
  any numeral family `a ↦ encode (φ/[‘↑a’])`. This is the **Σ₁ route** that audit r2 (fidelity N5,
  adversarial 5) pointed at: Foundation's `re_iff_sigma1` turns the r.e. predicate into a
  `𝚺₁-Predicate`, Foundation's `definability` shows the arithmetised substitution
  `a ↦ Bootstrapping.subst ?[numeral a] ⌜φ⌝` is a Σ₁-definable function, the two compose
  (`HierarchySymbol.DefinablePred.comp`), `re_iff_sigma1` turns the composite back into an r.e.
  predicate, and the quote identities `quote_numeralSubst` (`⌜φ/[‘↑a’]⌝ = subst ?[numeral a] ⌜φ⌝` at
  `ℕ`) and `quote_nat_eq_encode` (`⌜σ⌝ = Encodable.encode σ`, from Foundation's `quote_eq_encode`
  and `encode_emb`) identify the index with the `Encodable` code the recoverer reads;
* `not_provable_re_of_recoverer`: from a uniform recoverer `f` of the limits of an inductor over
  `paperDP T`, non-provability along the halting family is r.e. — `search_re` pulled back along
  the halting family, the domain rewritten by `exists_search_iff_lt_one` and the LI biconditional.
  **No coding hypothesis** (in repair round 1 this took `numeralSubst_code_computable haltCode`
  as an explicit hypothesis `hsub`; repair round 2 removed it);
* **`limit_non_recoverable_of_inductor`**, **`limit_non_recoverable`**: T6.2 for every inductor
  over `paperDP T`, and for FAF's paper LIA — provability would be r.e. and co-r.e., hence
  computable (`computable_iff_re_compl_re'`), against Church. **Proved outright** (sorry-free;
  axioms `propext`/`Classical.choice`/`Quot.sound`) since repair round 2; instance
  `limit_non_recoverable_ISigma1` at the mandate's `T := 𝗜𝚺₁`;
* `no_computable_modulus`: the mandate's corollary — no computable price table with a computable
  modulus of convergence to an inductor's limits over `paperDP T` (kind L); and, since repair
  round 3, **`no_computable_modulus_market`**: the same over FAF's own object, no `ComputableMarket`
  history with a computable modulus (through FAF's decomposition compiler
  `paperPrimeDecomposeCode_prim`, `paperPrimeDecomposeCode_encode`; audit r3 adversarial 2);
* **`convergence_rate_not_computable`** (repair round 3): **LI Proposition 5.5.1** — no computable
  convergence-rate function for any inductor over `paperDP T`; OPEN of record through repair
  round 2 "for want of the market-side search", which `paperPrimeDecomposeCode_prim` supplies:
  `rateSearch_re` (the search over the market's own quotes, r.e. in the arithmetic code), pulled
  back along the halting family exactly as T6.2. Non-vacuity: `convergence_rate_exists_classically`;
* `exists_computable_modulusFree_approximant`, `paper_modulusFree_approximant` (repair round 3,
  audit r3 fidelity B1): the **contrast** — without a modulus, the market's own quote table is a
  computable uniform approximant of every limit, so the source's modulus-free `𝓡(H) ⊊ 𝓢` is
  false (findings F4) and T6.2's impossibility rests on the modulus;
* `paperU1U2`: T6.1's `u1_u2_inductor` instantiated at FAF's paper LIA with `li-quote-lane`'s
  `ledgerSeq` (audit r2 N2); pinned at `a ≡ 1/2`, same-day publication, as
  `paperU1U2_half_sameDay`, with `ledgerSeq_half_sameDay_literal` showing the family is a real
  ledger literal somewhere (audit r3 adversarial 3).

`numeralSubst_code_computable` — `Computable fun a : ℕ ↦ Encodable.encode (φ/[‘↑a’])`, the coding
fact T6.2 rested on after repair round 1 — **is no longer load-bearing**: nothing in the package
depends on it since repair round 2. It stays as an OPEN statement of record (section (D) of
`li-projection-open.txt`): believed true (a primitive recursion over Foundation's `Nat.pair`-nested
codes, or the Σ₁ route above plus a "total function with r.e. graph is computable" lemma that
Mathlib lacks), and an FAF/Foundation API request, but not needed here.
-/

namespace Cleanroom.Li.LiProjection

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Filter Topology
open LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

/-! ## The halting family and Church's theorem along it -/

/-- Mathlib's halting predicate, transported to `ℕ` along the code of a `Nat.Partrec.Code`
(Foundation's `REPred.iff_decoded_pred` convention): `n` is the code of a program that halts on
input `0`.
Source: mandate T6.2 ("from `ComputablePred.halting_problem` and `re_complete`")
Kind: D
Fidelity: exact -/
def haltPred : ℕ → Prop := fun n =>
  (Encodable.decode (α := Nat.Partrec.Code) n).elim False (fun c => (c.eval 0).Dom)

/-- The halting predicate on `ℕ` is r.e. (Mathlib's `halting_problem_re`, decoded).
Source: mandate T6.2
Kind: L
Fidelity: exact -/
theorem haltPred_re : REPred haltPred :=
  REPred.iff_decoded_pred.mp (ComputablePred.halting_problem_re 0)

/-- The halting predicate on `ℕ` is not computable (Mathlib's `halting_problem`, decoded).
Source: mandate T6.2
Kind: L
Fidelity: exact -/
theorem haltPred_not_computable : ¬ ComputablePred haltPred := fun h =>
  ComputablePred.halting_problem 0 (ComputablePred.iff_decoded_pred.mpr h)

/-- Foundation's Σ₁ code of the halting predicate (`codeOfREPred`), a one-variable arithmetic
formula whose numeral instances `haltSentence a` are provable in `T` exactly when `a` halts.
Source: mandate T6.2; Foundation `Arithmetic/R0/Representation.lean` (`codeOfREPred`, `re_complete`)
Kind: D
Fidelity: exact -/
noncomputable def haltCode : ArithmeticSemisentence 1 := codeOfREPred haltPred

/-- The halting family of sentences: `haltSentence a := haltCode/[‘↑a’]`.
Source: mandate T6.2
Kind: D
Fidelity: exact -/
noncomputable def haltSentence (a : ℕ) : ArithmeticSentence := haltCode/[‘↑a’]

section Church

variable (T : ArithmeticTheory) [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-- Σ₁-completeness at the halting predicate: `a` halts iff `T ⊢ haltSentence a` (Foundation's
`re_complete`, which needs `𝗥₀ ⪯ T` and Σ₁-soundness — both from the section binders).
Source: mandate T6.2; Foundation `re_complete`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem halt_iff_provable (a : ℕ) : haltPred a ↔ T ⊢ haltSentence a :=
  re_complete (T := T) haltPred_re

/-- Provability in `T` along the halting family is recursively enumerable (it is the halting
predicate, which is r.e.).
Source: mandate T6.2 ("provability is r.e. (`re_complete`)")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem provable_haltCode_re : REPred (fun a : ℕ => T ⊢ haltSentence a) :=
  haltPred_re.of_eq (fun a => halt_iff_provable T a)

/-- **Church's theorem along the halting family.** Provability in `T` is not decidable along the
numeral instances of `haltCode`: a decision procedure would decide the halting problem
(`ComputablePred.halting_problem`). Proved outright; no computability of substitution on codes is
involved, because the reduction is at the level of the index `a`, not of sentence codes.
Source: mandate T6.2 ("Church: `¬ ComputablePred (fun σ => T ⊢ σ)`; if Foundation does not expose that last fact, prove it from `ComputablePred.halting_problem` and `re_complete`"); Church 1936
Kind: C (Mathlib's `halting_problem` transported along Foundation's `re_complete` — a one-step composition, re-kinded from P in repair round 2, audit r2 fidelity N1 / adversarial 3)
Fidelity: variant: along the halting family `a ↦ haltCode/[‘↑a’]` (the strongest form for the reduction below), not over all sentence codes
Hyps: (a) -/
theorem church_haltCode : ¬ ComputablePred (fun a : ℕ => T ⊢ haltSentence a) := fun h =>
  haltPred_not_computable (h.of_eq (fun a => (halt_iff_provable T a).symm))

end Church

/-! ## The search on a uniform approximant -/

/-- **The search is exact.** For a real `L` and a sequence `F` with `|F k − L| ≤ 1/(k+1)` for all
`k`: some `k` has `(k+1)·F k < k` (i.e. `F k < 1 − 1/(k+1)`) iff `L < 1`. (⟹) `L ≤ F k + 1/(k+1) < 1`;
(⟸) take `k + 1 > 2/(1 − L)`.
Source: mandate T6.2 ("search `k` with `f σ k < 1 − 2/(k+1)`", sharpened to `1 − 1/(k+1)`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem exists_search_iff_lt_one {L : ℝ} (F : ℕ → ℚ)
    (happrox : ∀ k : ℕ, |(F k : ℝ) - L| ≤ 1 / (k + 1)) :
    (∃ k : ℕ, ((k + 1 : ℕ) : ℚ) * F k < (k : ℚ)) ↔ L < 1 := by
  constructor
  · rintro ⟨k, hk⟩
    have hkR : ((k : ℝ) + 1) * (F k : ℝ) < k := by exact_mod_cast hk
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h1 : L - F k ≤ 1 / ((k : ℝ) + 1) := by
      have := (abs_le.mp (happrox k)).1
      linarith
    have h2 : (L - F k) * ((k : ℝ) + 1) ≤ 1 := (le_div_iff₀ hpos).mp h1
    nlinarith
  · intro hL
    have h1L : (0 : ℝ) < 1 - L := by linarith
    obtain ⟨k, hk⟩ := exists_nat_gt (2 / (1 - L))
    refine ⟨k, ?_⟩
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hk' : 2 / (1 - L) < (k : ℝ) + 1 := by linarith
    have h2 : 2 < ((k : ℝ) + 1) * (1 - L) := (div_lt_iff₀ h1L).mp hk'
    have h3 : (F k : ℝ) - L ≤ 1 / ((k : ℝ) + 1) := (abs_le.mp (happrox k)).2
    have h4 : ((F k : ℝ) - L) * ((k : ℝ) + 1) ≤ 1 := (le_div_iff₀ hpos).mp h3
    have h5 : ((k : ℝ) + 1) * (F k : ℝ) < k := by nlinarith
    exact_mod_cast h5

/-! ## The search is r.e. in the sentence code -/

/-- The search bit of a recoverer `f` at sentence code `c` and precision `k`: `true` iff
`(k+1) · f c k < k`, i.e. iff the approximant is below `1 − 1/(k+1)`. Generic in the decision
procedure `dec` for `≤` on `ℚ` (the one FAF's `ratLE_prim` certifies). (Repair round 2: indexed
by the code `c`, not by the halting index `a`.)
Source: mandate T6.2 (the r.e. search); none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def searchBit (f : ℕ → ℕ → ℚ) (dec : DecidablePred fun p : ℚ × ℚ => p.1 ≤ p.2)
    (c k : ℕ) : Bool :=
  !(@decide _ (dec (((k : ℕ) : ℚ), ((k + 1 : ℕ) : ℚ) * f c k)))

/-- `searchBit_iff`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma searchBit_iff (f : ℕ → ℕ → ℚ) (dec : DecidablePred fun p : ℚ × ℚ => p.1 ≤ p.2) (c k : ℕ) :
    searchBit f dec c k = true ↔ ((k + 1 : ℕ) : ℚ) * f c k < (k : ℚ) := by
  simp [searchBit, not_le]

/-- **The search is r.e. in the code.** For a computable `f : ℕ → ℕ → ℚ`, the predicate
`fun c ↦ ∃ k, (k+1)·f c k < k` on sentence codes is recursively enumerable: `Partrec.rfind` on the
search bit, which is computable through FAF's `ratMul_prim`/`ratNatCast_prim`/`ratLE_prim`.
Source: mandate T6.2 (proof shape)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem search_re (f : ℕ → ℕ → ℚ) (hf : Computable (fun p : ℕ × ℕ => f p.1 p.2)) :
    REPred (fun c : ℕ => ∃ k : ℕ, ((k + 1 : ℕ) : ℚ) * f c k < (k : ℚ)) := by
  have hX : Computable (fun p : ℕ × ℕ => ((p.2 + 1 : ℕ) : ℚ)) :=
    (ratNatCast_prim.comp (Primrec.succ.comp Primrec.snd)).to_comp
  have hA : Computable (fun p : ℕ × ℕ => ((p.2 + 1 : ℕ) : ℚ) * f p.1 p.2) :=
    ratMul_prim.to_comp.comp hX hf
  have hB : Computable (fun p : ℕ × ℕ => ((p.2 : ℕ) : ℚ)) :=
    (ratNatCast_prim.comp Primrec.snd).to_comp
  obtain ⟨dec, hprim⟩ : PrimrecPred (fun p : ℚ × ℚ => p.1 ≤ p.2) :=
    PrimrecRel.comp ratLE_prim Primrec.fst Primrec.snd
  have hle : Computable (fun p : ℕ × ℕ => @decide _ (dec (((p.2 : ℕ) : ℚ),
      ((p.2 + 1 : ℕ) : ℚ) * f p.1 p.2))) :=
    hprim.to_comp.comp (Computable.pair hB hA)
  have hg : Computable₂ (searchBit f dec) := Primrec.not.to_comp.comp hle
  have hdom : ∀ c, (Nat.rfind (searchBit f dec c : ℕ →. Bool)).Dom ↔
      ∃ n, searchBit f dec c n = true := by
    intro c
    rw [Nat.rfind_dom]
    constructor
    · rintro ⟨n, hn, -⟩
      exact ⟨n, (Part.mem_some_iff.mp hn).symm⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, Part.mem_some_iff.mpr hn.symm, fun _ => trivial⟩
  refine (Partrec.rfind hg.partrec₂).dom_re.of_eq fun c => ?_
  rw [hdom c]
  simp only [searchBit_iff]

/-! ## R.e. predicates pull back along a numeral family (the Σ₁ route) -/

/-- Foundation's Gödel number of a sentence, read in the standard model `ℕ`, is its `Encodable` code
(`Semiformula.quote_eq_encode` for syntactic formulas and `encode_emb` for the embedding of a
sentence). This is what identifies the index the recoverer reads with the index Foundation's
arithmetised syntax computes with.
Source: none: infrastructure (Foundation `Bootstrapping/Syntax/Formula/Coding.lean` `quote_eq_encode`, `Basic/Coding.lean` `encode_emb`)
Kind: L
Fidelity: exact -/
lemma quote_nat_eq_encode (σ : ArithmeticSentence) : (⌜σ⌝ : ℕ) = Encodable.encode σ := by
  simp [Sentence.quote_def, Semiformula.quote_eq_encode, Semiformula.encode_emb]

/-- The Gödel number of a numeral instance `φ/[‘↑a’]` at `ℕ` is Foundation's arithmetised
substitution `Bootstrapping.subst ?[numeral a] ⌜φ⌝` (the identity Foundation's own
`Incompleteness/Halting.lean` uses inside provability).
Source: none: infrastructure (Foundation `typed_quote_substs`, `Rewriting.emb_subst_eq_subst_coe₁`)
Kind: L
Fidelity: exact -/
lemma quote_numeralSubst (φ : ArithmeticSemisentence 1) (a : ℕ) :
    (⌜(φ/[‘↑a’] : ArithmeticSentence)⌝ : ℕ) =
      Bootstrapping.subst ℒₒᵣ ?[Bootstrapping.Arithmetic.numeral a] (⌜φ⌝ : ℕ) := by
  simp [Sentence.quote_def, Rewriting.emb_subst_eq_subst_coe₁, Semiformula.quote_def]

/-- **R.e. predicates on sentence codes pull back along a numeral family.** For a fixed
`φ : ArithmeticSemisentence 1` and any r.e. `E : ℕ → Prop`, the predicate
`a ↦ E (Encodable.encode (φ/[‘↑a’]))` is r.e. The route avoids any Mathlib-`Computable`
statement about substitution on codes: `re_iff_sigma1` makes `E` a `𝚺₁-Predicate` of the standard
model; Foundation's `definability` makes `a ↦ Bootstrapping.subst ?[numeral a] ⌜φ⌝` a Σ₁-definable
function; `HierarchySymbol.DefinablePred.comp` composes them; `re_iff_sigma1` turns the composite
back into an r.e. predicate; `quote_numeralSubst` and `quote_nat_eq_encode` identify its argument
with `Encodable.encode (φ/[‘↑a’])`. This is the lemma that replaces the coding fact
`numeralSubst_code_computable` in T6.2 (audit r2 fidelity N5 / adversarial 5, the lead; repair
round 2, done).
Source: mandate T6.2 (the "numeral substitution computable on sentence codes" step, discharged by the Σ₁ route instead); Foundation `Incompleteness/Halting.lean` (the pattern)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem rePred_comp_numeralSubst (φ : ArithmeticSemisentence 1) {E : ℕ → Prop} (hE : REPred E) :
    REPred (fun a : ℕ => E (Encodable.encode (φ/[‘↑a’] : ArithmeticSentence))) := by
  have h1 : 𝚺₁-Predicate E := re_iff_sigma1.mp hE
  have h2 : 𝚺₁-Predicate (fun a : ℕ =>
      E (Bootstrapping.subst ℒₒᵣ ?[Bootstrapping.Arithmetic.numeral a] (⌜φ⌝ : ℕ))) :=
    HierarchySymbol.DefinablePred.comp h1 (by definability)
  refine (re_iff_sigma1.mpr h2).of_eq fun a => ?_
  rw [← quote_nat_eq_encode, quote_numeralSubst]

/-! ## The market-side search (LI Proposition 5.5.1; repair round 3) -/

/-- The code of the decomposition of a sentence is FAF's decomposition compiler at the sentence's
code: `paperPrimeDecomposeCode ⌜σ⌝ = ⌜paperPrimeDecompose σ⌝` (FAF's `paperPrimeDecomposeCode_spec`
at `Rewriting.emb σ`, with Foundation's `encode_emb`). This is the map from the arithmetic index a
rate function or a modulus reads to the propositional index the market's quote table reads; FAF
proves it primitive recursive (`paperPrimeDecomposeCode_prim`), which is what makes a search over
the market's own quotes r.e. in the *arithmetic* code — the "market-side search" that kept LI
Proposition 5.5.1 OPEN through repair round 2.
Source: none: infrastructure (FAF `Construction/Paper/FirstOrder.lean` `paperPrimeDecomposeCode_spec`, `paperPrimeDecomposeCode_prim`)
Kind: L
Fidelity: exact -/
lemma paperPrimeDecomposeCode_encode (σ : ArithmeticSentence) :
    paperPrimeDecomposeCode (Encodable.encode σ) =
      Encodable.encode (paperPrimeDecompose σ) := by
  have h := paperPrimeDecomposeCode_spec (Rewriting.emb σ)
  simpa [Semiformula.encode_emb] using h

/-- The rate-search bit of a rate function `f` and a quote table `q` at sentence code `c` and
pair `z = ⟨k, n⟩`: `true` iff `f c k < n` and `(k+1) · q n (paperPrimeDecomposeCode c) ≤ k`, i.e. iff
day `n` is past the rate at precision `k` and the market's price of the decomposition of `c` on
day `n` is at most `1 − 1/(k+1)`. Generic in the decision procedures for `<` on `ℕ` and `≤` on `ℚ`
(the ones Mathlib's `Primrec.nat_lt` and FAF's `ratLE_prim` certify).
Source: LI Proposition 5.5.1 (proof shape); none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def rateBit (f : ℕ → ℕ → ℕ) (q : ℕ → ℕ → ℚ)
    (decLt : DecidablePred fun p : ℕ × ℕ => p.1 < p.2)
    (dec : DecidablePred fun p : ℚ × ℚ => p.1 ≤ p.2) (c z : ℕ) : Bool :=
  (@decide _ (decLt (f c z.unpair.1, z.unpair.2))) &&
    (@decide _ (dec (((z.unpair.1 + 1 : ℕ) : ℚ) * q z.unpair.2 (paperPrimeDecomposeCode c),
      ((z.unpair.1 : ℕ) : ℚ))))

/-- `rateBit_iff`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma rateBit_iff (f : ℕ → ℕ → ℕ) (q : ℕ → ℕ → ℚ)
    (decLt : DecidablePred fun p : ℕ × ℕ => p.1 < p.2)
    (dec : DecidablePred fun p : ℚ × ℚ => p.1 ≤ p.2) (c z : ℕ) :
    rateBit f q decLt dec c z = true ↔
      f c z.unpair.1 < z.unpair.2 ∧
        ((z.unpair.1 + 1 : ℕ) : ℚ) * q z.unpair.2 (paperPrimeDecomposeCode c) ≤ (z.unpair.1 : ℚ) := by
  simp [rateBit]

/-- **The rate search is r.e. in the sentence code.** For a computable `f : ℕ → ℕ → ℕ` and a market
program `M` (FAF's `MarketComputation`, the operational form of `ComputableMarket`), the predicate
"some precision `k` and some day `n > f c k` at which the market's price of the decomposition of
`c` is at most `1 − 1/(k+1)`" is recursively enumerable in `c`: `Partrec.rfind` on `rateBit` over
the pair `⟨k, n⟩`, computable through FAF's `paperPrimeDecomposeCode_prim`, the market program
(`marketComputation_quote_computable'`) and `ratMul_prim`/`ratNatCast_prim`/`ratLE_prim`.
Source: LI Proposition 5.5.1 (proof shape: "search the market, contradict Church")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem rateSearch_re {P : History} (M : MarketComputation P) (f : ℕ → ℕ → ℕ)
    (hf : Computable (fun p : ℕ × ℕ => f p.1 p.2)) :
    REPred (fun c : ℕ => ∃ z : ℕ, f c z.unpair.1 < z.unpair.2 ∧
      ((z.unpair.1 + 1 : ℕ) : ℚ) * M.quote z.unpair.2 (paperPrimeDecomposeCode c) ≤ (z.unpair.1 : ℚ)) := by
  have hc : Computable fun p : ℕ × ℕ => p.1 := Computable.fst
  have hk : Computable fun p : ℕ × ℕ => p.2.unpair.1 :=
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hn : Computable fun p : ℕ × ℕ => p.2.unpair.2 :=
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hfk : Computable fun p : ℕ × ℕ => f p.1 p.2.unpair.1 := hf.comp (Computable.pair hc hk)
  obtain ⟨decLt, hltprim⟩ : PrimrecRel ((· < ·) : ℕ → ℕ → Prop) := Primrec.nat_lt
  have hlt : Computable fun p : ℕ × ℕ => @decide _ (decLt (f p.1 p.2.unpair.1, p.2.unpair.2)) :=
    hltprim.to_comp.comp (Computable.pair hfk hn)
  have hq : Computable fun p : ℕ × ℕ => M.quote p.2.unpair.2 (paperPrimeDecomposeCode p.1) := by
    have hd : Computable fun w : ℕ => w.unpair.2.unpair.2 :=
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp
    have hg : Computable fun w : ℕ => paperPrimeDecomposeCode w.unpair.1 :=
      (paperPrimeDecomposeCode_prim.comp (Primrec.fst.comp Primrec.unpair)).to_comp
    have h1 := marketComputation_quote_computable' M hd hg
    have hpair : Computable fun p : ℕ × ℕ => Nat.pair p.1 p.2 :=
      Primrec₂.natPair.to_comp.comp Computable.fst Computable.snd
    exact (h1.comp hpair).of_eq fun p => by simp
  have hX : Computable (fun p : ℕ × ℕ => ((p.2.unpair.1 + 1 : ℕ) : ℚ)) :=
    (ratNatCast_prim.comp (Primrec.succ.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))).to_comp
  have hA : Computable (fun p : ℕ × ℕ =>
      ((p.2.unpair.1 + 1 : ℕ) : ℚ) * M.quote p.2.unpair.2 (paperPrimeDecomposeCode p.1)) :=
    ratMul_prim.to_comp.comp hX hq
  have hB : Computable (fun p : ℕ × ℕ => ((p.2.unpair.1 : ℕ) : ℚ)) :=
    (ratNatCast_prim.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))).to_comp
  obtain ⟨dec, hprim⟩ : PrimrecPred (fun p : ℚ × ℚ => p.1 ≤ p.2) :=
    PrimrecRel.comp ratLE_prim Primrec.fst Primrec.snd
  have hle : Computable (fun p : ℕ × ℕ => @decide _ (dec (
      ((p.2.unpair.1 + 1 : ℕ) : ℚ) * M.quote p.2.unpair.2 (paperPrimeDecomposeCode p.1),
      ((p.2.unpair.1 : ℕ) : ℚ)))) :=
    hprim.to_comp.comp (Computable.pair hA hB)
  have hg : Computable₂ (rateBit f M.quote decLt dec) :=
    Primrec.and.to_comp.comp hlt hle
  have hdom : ∀ c, (Nat.rfind (rateBit f M.quote decLt dec c : ℕ →. Bool)).Dom ↔
      ∃ z, rateBit f M.quote decLt dec c z = true := by
    intro c
    rw [Nat.rfind_dom]
    constructor
    · rintro ⟨n, hn, -⟩
      exact ⟨n, (Part.mem_some_iff.mp hn).symm⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, Part.mem_some_iff.mpr hn.symm, fun _ => trivial⟩
  refine (Partrec.rfind hg.partrec₂).dom_re.of_eq fun c => ?_
  rw [hdom c]
  simp only [rateBit_iff]

/-! ## T6.2 -/

section Recoverer

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-- **A uniform recoverer makes non-provability r.e. along the halting family.** If `f` is a
computable uniform approximant of the limiting beliefs of an inductor `P` over `paperDP T`, then
`fun a ↦ ¬ T ⊢ haltSentence a` is r.e.: the search `∃ k, (k+1)·f c k < k` is r.e. in the code `c`
(`search_re`), pulls back along the halting family (`rePred_comp_numeralSubst`), and by
`exists_search_iff_lt_one` finds exactly the `a` with `P_∞(σ_a) < 1`, i.e. (LI half,
`limitingBelief_paperPrime_eq_one_iff`) the unprovable ones. No coding hypothesis (repair round 2;
in round 1 this took `numeralSubst_code_computable haltCode` as an explicit hypothesis).
Source: mandate T6.2 (proof shape); [[anson-inventory]] 029
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem not_provable_re_of_recoverer (P : History) [IsLogicalInductor P (paperDP T)]
    (f : ℕ → ℕ → ℚ) (hf : Computable (fun p : ℕ × ℕ => f p.1 p.2))
    (happrox : ∀ (σ : ArithmeticSentence) (k : ℕ),
      |(f (Encodable.encode σ) k : ℝ) - limitingBelief P (paperPrimeDecompose σ)| ≤ 1 / (k + 1)) :
    REPred (fun a : ℕ => ¬ T ⊢ haltSentence a) := by
  refine (rePred_comp_numeralSubst haltCode (search_re f hf)).of_eq fun a => ?_
  show (∃ k : ℕ, ((k + 1 : ℕ) : ℚ) * f (Encodable.encode (haltSentence a)) k < (k : ℚ)) ↔ _
  rw [exists_search_iff_lt_one (fun k => f (Encodable.encode (haltSentence a)) k)
    (fun k => happrox (haltSentence a) k)]
  constructor
  · intro hlt hprov
    have := (limitingBelief_paperPrime_eq_one_iff T P (haltSentence a)).mpr hprov
    linarith
  · intro hnot
    exact limitingBelief_paperPrime_lt_one_of_unprovable T P _ hnot

/-- **T6.2 for every inductor over `paperDP T`: uniform limit non-recoverability.** No computable
`f : ℕ → ℕ → ℚ` has `|f ⌜σ⌝ k − P_∞(⌜σ⌝)| ≤ 1/(k+1)` for all sentences `σ` and all `k`: with such
an `f`, provability along the halting family would be r.e. (`provable_haltCode_re`) and co-r.e.
(`not_provable_re_of_recoverer`), hence decidable, against `church_haltCode`. Proved outright
(repair round 2: the Σ₁ route `rePred_comp_numeralSubst` replaced the coding fact). The sentence
`σ` enters the decomposition through `Rewriting.emb` (`paperPrimeDecompose` takes an
`ArithmeticProposition`; `#check` prints `paperPrimeDecompose (Rewriting.emb σ)`), the same
embedding `limitingBelief_paperPrime_eq_one_iff` uses, so `T ⊢ σ` and the market side refer to the
same sentence (audit r2 adversarial 6).
Source: [[anson-inventory]] 029 (chat 11 L4555–4605, the uniform form with a computable modulus — the modulus-free claim is false, findings F4); [[trust-lab-inventory]] 067; [[root-deference-inventory]] 024 (R1); [[deference-in-logical-induction-v6]] §4.1; mandate T6.2
Kind: C
Fidelity: stronger: every inductor over `paperDP T`, not only the paper LIA; variant: uniform recoverability **with a computable modulus** (`|f ⌜σ⌝ k − P_∞| ≤ 1/(k+1)`) — the modulus is what carries the impossibility: without it the market's own quote table is a computable uniform approximant of every limit (`exists_computable_modulusFree_approximant` below), so the source's modulus-free `𝓡(H) ⊊ 𝓢` is false rather than ill-posed (findings F4; audit r3 fidelity B1)
Hyps: (a) throughout -/
theorem limit_non_recoverable_of_inductor (P : History) [IsLogicalInductor P (paperDP T)] :
    ¬ ∃ f : ℕ → ℕ → ℚ, Computable (fun p : ℕ × ℕ => f p.1 p.2) ∧
      ∀ (σ : ArithmeticSentence) (k : ℕ),
        |(f (Encodable.encode σ) k : ℝ) - limitingBelief P (paperPrimeDecompose σ)| ≤ 1 / (k + 1) := by
  rintro ⟨f, hf, happrox⟩
  apply church_haltCode T
  exact ComputablePred.computable_iff_re_compl_re'.mpr
    ⟨provable_haltCode_re T, not_provable_re_of_recoverer T P f hf happrox⟩

/-- **T6.2, the mandate's statement: uniform limit non-recoverability for FAF's paper LIA.** No
computable `f : ℕ → ℕ → ℚ` approximates every limiting belief of `liaHistory (paperDP T)` uniformly
(`|f ⌜σ⌝ k − P_∞(⌜σ⌝)| ≤ 1/(k+1)`): the repaired No-Forced-Trust. Binders are those of Foundation's
`Halting.lean` (Church's theorem needs Σ₁-soundness), inhabited by `𝗜𝚺₁`
(`limit_non_recoverable_ISigma1`). Proved outright since repair round 2. `σ` enters through
`Rewriting.emb`, as in `limit_non_recoverable_of_inductor`.
Source: [[anson-inventory]] 029 (chat 11 L4555–4605, the uniform form with a computable modulus — the modulus-free claim is false, findings F4); [[trust-lab-inventory]] 067; [[root-deference-inventory]] 024 (R1); [[deference-in-logical-induction-v6]] §4.1
Kind: C
Fidelity: variant: uniform recoverability **with a computable modulus** — the modulus carries the impossibility; without it the market's own table approximates every limit (`paper_modulusFree_approximant`; findings F4, audit r3 fidelity B1)
Hyps: (a) throughout -/
theorem limit_non_recoverable :
    ¬ ∃ f : ℕ → ℕ → ℚ, Computable (fun p : ℕ × ℕ => f p.1 p.2) ∧
      ∀ (σ : ArithmeticSentence) (k : ℕ),
        |(f (Encodable.encode σ) k : ℝ) -
            limitingBelief (liaHistory (paperDP T)) (paperPrimeDecompose σ)| ≤ 1 / (k + 1) :=
  haveI : IsLogicalInductor (liaHistory (paperDP T)) (paperDP T) :=
    LIA_is_logical_inductor _ (paperDP_computable _)
  limit_non_recoverable_of_inductor T (liaHistory (paperDP T))

/-- **The mandate's corollary (kind L): no computable modulus of convergence.** No computable price
table `A : ℕ → ℕ → ℚ` (day, sentence code) together with a computable modulus `m : ℕ → ℕ → ℕ`
(sentence code, precision) has `|A n ⌜σ⌝ − P_∞(⌜σ⌝)| ≤ 1/(k+1)` for all `n ≥ m ⌜σ⌝ k`, for any
inductor `P` over `paperDP T`: `f ⌜σ⌝ k := A (m ⌜σ⌝ k) ⌜σ⌝` would be a computable uniform
recoverer. In particular no computable `A` whose price sequences converge to `P`'s limits can
*certify* its own convergence (the source's "no efficiently-checkable relation forces
`A_∞ = H_∞` on all undecidables"). `A` need not be related to `P` otherwise.
Source: mandate T6.2 ("any computable `A` whose price sequences had a computable modulus of convergence to `H`'s limits would give such an `f`"); [[root-deference-inventory]] 024 (R1)
Kind: L
Fidelity: exact (over computable tables `A : ℕ → ℕ → ℚ` on (day, code); every `ComputableMarket` history yields such a table through its `MarketComputation.quote` composed with FAF's decomposition compiler `paperPrimeDecomposeCode` — that is the corollary `no_computable_modulus_market` below; repair round 3 corrected the earlier clause "every `MachineRatCodes` sequence is such a table", a `MachineRatCodes q` being one sequence, not a table — audit r3 adversarial 2)
Hyps: (a) -/
theorem no_computable_modulus (P : History) [IsLogicalInductor P (paperDP T)] :
    ¬ ∃ (A : ℕ → ℕ → ℚ) (m : ℕ → ℕ → ℕ), Computable (fun p : ℕ × ℕ => A p.1 p.2) ∧
      Computable (fun p : ℕ × ℕ => m p.1 p.2) ∧
      ∀ (σ : ArithmeticSentence) (k n : ℕ), m (Encodable.encode σ) k ≤ n →
        |(A n (Encodable.encode σ) : ℝ) - limitingBelief P (paperPrimeDecompose σ)| ≤ 1 / (k + 1) := by
  rintro ⟨A, m, hA, hm, hmod⟩
  apply limit_non_recoverable_of_inductor T P
  refine ⟨fun c k => A (m c k) c, ?_, fun σ k => hmod σ k _ le_rfl⟩
  exact hA.comp (Computable.pair hm Computable.fst)

/-- **The mandate's corollary over FAF's own object: no `ComputableMarket` history with a computable
modulus.** No history `A` that is a `ComputableMarket` (FAF's field: a computable rational quote
table with `A n φ = quote n ⌜φ⌝` exactly), together with a computable modulus `m : ℕ → ℕ → ℕ`
(sentence code, precision), has `|A n (paperPrimeDecompose σ) − P_∞(paperPrimeDecompose σ)| ≤ 1/(k+1)`
for all `n ≥ m ⌜σ⌝ k`, for any inductor `P` over `paperDP T`: the table `(n, c) ↦ quote n
(paperPrimeDecomposeCode c)` is computable (`marketComputation_quote_computable'`,
`paperPrimeDecomposeCode_prim`) and is exactly the table `no_computable_modulus` forbids
(`paperPrimeDecomposeCode_encode`). This is the FAF object the mandate's sentence "any computable `A`
whose price sequences had a computable modulus" names; `A` need not be related to `P` otherwise (in
particular `A := P` is allowed: no inductor can certify its own convergence by a computable modulus).
Source: mandate T6.2 ("any computable `A` whose price sequences had a computable modulus of convergence to `H`'s limits would give such an `f`"); [[root-deference-inventory]] 024 (R1); audit r3 adversarial 2
Kind: C
Fidelity: exact (over FAF's `ComputableMarket`; a computable modulus indexed by the arithmetic sentence code)
Hyps: (a) -/
theorem no_computable_modulus_market (P : History) [IsLogicalInductor P (paperDP T)] :
    ¬ ∃ (A : History) (m : ℕ → ℕ → ℕ), ComputableMarket A ∧
      Computable (fun p : ℕ × ℕ => m p.1 p.2) ∧
      ∀ (σ : ArithmeticSentence) (k n : ℕ), m (Encodable.encode σ) k ≤ n →
        |A n (paperPrimeDecompose σ) - limitingBelief P (paperPrimeDecompose σ)| ≤ 1 / (k + 1) := by
  rintro ⟨A, m, hA, hm, hmod⟩
  obtain ⟨M⟩ := hA.nonemptyComputation
  apply no_computable_modulus T P
  refine ⟨fun n c => M.quote n (paperPrimeDecomposeCode c), m, ?_, hm, ?_⟩
  · have hfst : Computable fun z : ℕ => z.unpair.1 :=
      (Primrec.fst.comp Primrec.unpair).to_comp
    have hsnd : Computable fun z : ℕ => paperPrimeDecomposeCode z.unpair.2 :=
      (paperPrimeDecomposeCode_prim.comp (Primrec.snd.comp Primrec.unpair)).to_comp
    have h1 : Computable fun z : ℕ => M.quote z.unpair.1 (paperPrimeDecomposeCode z.unpair.2) :=
      marketComputation_quote_computable' M hfst hsnd
    have hpair : Computable fun p : ℕ × ℕ => Nat.pair p.1 p.2 :=
      Primrec₂.natPair.to_comp.comp Computable.fst Computable.snd
    exact (h1.comp hpair).of_eq fun p => by simp
  · intro σ k n hn
    show |(M.quote n (paperPrimeDecomposeCode (Encodable.encode σ)) : ℝ) -
      limitingBelief P (paperPrimeDecompose σ)| ≤ 1 / (k + 1)
    rw [paperPrimeDecomposeCode_encode, ← M.quote_exact]
    exact hmod σ k n hn

/-! ### LI Proposition 5.5.1: uncomputable convergence rates (the extension; OPEN of record through
repair round 2, proved in repair round 3) -/

/-- **Non-vacuity of `convergence_rate_not_computable`.** The rate clause alone is satisfiable,
classically: for every inductor over `paperDP T` there IS a function `f : ℕ → ℕ → ℕ` with
`P n (paperPrimeDecompose σ) > 1 − 1/(k+1)` for all `n > f ⌜σ⌝ k` whenever `T ⊢ σ`, because on
theorems the price converges to `1` (`limitingBelief_paperPrime_of_provable`,
`lic_limitingBelief_tendsto`) and a threshold can be chosen for each `(σ, k)`. So the content of
`convergence_rate_not_computable` is its `Computable` conjunct, not an unsatisfiable rate clause
(the check audit r3 adversarial made for `no_computable_modulus` in `ModulusInhabited.lean`).
Source: LI Proposition 5.5.1 (non-vacuity of the hypothesis package)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem convergence_rate_exists_classically (P : History) [IsLogicalInductor P (paperDP T)] :
    ∃ f : ℕ → ℕ → ℕ, ∀ (σ : ArithmeticSentence) (k n : ℕ), T ⊢ σ → f (Encodable.encode σ) k < n →
      1 - 1 / ((k : ℝ) + 1) < P n (paperPrimeDecompose σ) := by
  classical
  have hthr : ∀ (σ : ArithmeticSentence) (k : ℕ), T ⊢ σ →
      ∃ N : ℕ, ∀ n, N < n → 1 - 1 / ((k : ℝ) + 1) < P n (paperPrimeDecompose σ) := by
    intro σ k hprov
    have hconv : ConvergesTo (fun n => P n (paperPrimeDecompose σ)) 1 := by
      have h := lic_limitingBelief_tendsto P (paperDP T) (paperDP_hworld T) (paperPrimeDecompose σ)
      rwa [limitingBelief_paperPrime_of_provable T P σ hprov] at h
    have hlt : (1 : ℝ) - 1 / ((k : ℝ) + 1) < 1 := by
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hconv.eventually_const_lt hlt)
    exact ⟨N, fun n hn => hN n hn.le⟩
  choose! N hN using hthr
  refine ⟨fun c k => (Encodable.decode (α := ArithmeticSentence) c).elim 0 (fun σ => N σ k), ?_⟩
  intro σ k n hprov hn
  have hn' : N σ k < n := by simpa using hn
  exact hN σ k hprov n hn'

/-- **LI Proposition 5.5.1 over `paperDP T`: convergence rates are not computable.** No computable
`f : ℕ → ℕ → ℕ` has `P n (paperPrimeDecompose σ) > 1 − 1/(k+1)` for all `n > f ⌜σ⌝ k` whenever
`T ⊢ σ`, for any inductor `P` over `paperDP T`. Proof: with such an `f`, the predicate "`∃ k n,
f ⌜σ⌝ k < n ∧ P n (paperPrimeDecompose σ) ≤ 1 − 1/(k+1)`" holds iff `T ⊬ σ` — (⟹) a provable `σ`
has every such price above the bound by the rate hypothesis; (⟸) an unprovable `σ` has limit `< 1`
(`limitingBelief_paperPrime_lt_one_of_unprovable`), so for some `k` the limit is below
`1 − 1/(k+1)` and, the prices converging (`lic_limitingBelief_tendsto`), some day past the rate is
too — and it is r.e. in `⌜σ⌝` through the market's own quote table (`rateSearch_re`, FAF's
`ComputableMarket` field of the inductor, `paperPrimeDecomposeCode_encode`). Pulled back along the
halting family (`rePred_comp_numeralSubst`), non-provability is r.e.; provability is r.e.
(`provable_haltCode_re`); so it is decidable, against `church_haltCode`. The paper's `ε ∈ ℚ⁺` is
`1/(k+1)`; sentences enter by `Encodable` code, through `Rewriting.emb` as in T6.2. Not true for a
trivial reason: `convergence_rate_exists_classically`.
Source: [[fixpoint-lit-inventory]] 095; [[vq-wiki-2-inventory]] 015 (`main.tex:2663–2708`, LI Proposition 5.5.1: "Let `P̄` be a logical inductor over a theory `Γ` that represents computable functions, and `f : S × ℚ⁺ → ℕ` such that for every `φ`, if `Γ ⊢ φ` then `P_n(φ) > 1 − ε` for all `n > f(φ, ε)`. Then `f` is not computable."); mandate (the extension)
Kind: C
Fidelity: exact (over `paperDP T` with Foundation's `Halting.lean` binders in place of "represents computable functions"; codes in place of sentences; `ε = 1/(k+1)`)
Hyps: (a) throughout -/
theorem convergence_rate_not_computable (P : History) [IsLogicalInductor P (paperDP T)] :
    ¬ ∃ f : ℕ → ℕ → ℕ, Computable (fun p : ℕ × ℕ => f p.1 p.2) ∧
      ∀ (σ : ArithmeticSentence) (k n : ℕ), T ⊢ σ → f (Encodable.encode σ) k < n →
        1 - 1 / ((k : ℝ) + 1) < P n (paperPrimeDecompose σ) := by
  rintro ⟨f, hf, hrate⟩
  obtain ⟨M⟩ :=
    (inferInstance : IsLogicalInductor P (paperDP T)).marketComputable.nonemptyComputation
  apply church_haltCode T
  refine ComputablePred.computable_iff_re_compl_re'.mpr ⟨provable_haltCode_re T, ?_⟩
  refine (rePred_comp_numeralSubst haltCode (rateSearch_re M f hf)).of_eq fun a => ?_
  show (∃ z : ℕ, f (Encodable.encode (haltSentence a)) z.unpair.1 < z.unpair.2 ∧
      ((z.unpair.1 + 1 : ℕ) : ℚ) *
        M.quote z.unpair.2 (paperPrimeDecomposeCode (Encodable.encode (haltSentence a))) ≤
          (z.unpair.1 : ℚ)) ↔ _
  rw [paperPrimeDecomposeCode_encode]
  constructor
  · rintro ⟨z, hkn, hle⟩ hprov
    have h1 := hrate (haltSentence a) z.unpair.1 z.unpair.2 hprov hkn
    rw [M.quote_exact] at h1
    have hleR : (((z.unpair.1 + 1 : ℕ) : ℚ) : ℝ) * (M.quote z.unpair.2
        (Encodable.encode (paperPrimeDecompose (haltSentence a))) : ℝ) ≤ ((z.unpair.1 : ℕ) : ℝ) := by
      exact_mod_cast hle
    set k : ℕ := z.unpair.1 with hkdef
    set q : ℝ := (M.quote z.unpair.2 (Encodable.encode (paperPrimeDecompose (haltSentence a))) : ℝ)
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h2 : (1 : ℝ) - 1 / ((k : ℝ) + 1) = (k : ℝ) / ((k : ℝ) + 1) := by
      field_simp
      ring
    rw [h2] at h1
    have h3 : (k : ℝ) < q * ((k : ℝ) + 1) := (div_lt_iff₀ hpos).mp h1
    push_cast at hleR
    nlinarith
  · intro hnot
    have hlt := limitingBelief_paperPrime_lt_one_of_unprovable T P _ hnot
    set L := limitingBelief P (paperPrimeDecompose (haltSentence a)) with hL
    have h1L : (0 : ℝ) < 1 - L := by linarith
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / (1 - L))
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hk' : 1 / (1 - L) < (k : ℝ) + 1 := by linarith
    have hLk : L < 1 - 1 / ((k : ℝ) + 1) := by
      have : 1 / ((k : ℝ) + 1) < 1 - L := by
        rw [div_lt_iff₀ hpos]
        rw [div_lt_iff₀ h1L] at hk'
        linarith
      linarith
    have hconv : ConvergesTo (fun n => P n (paperPrimeDecompose (haltSentence a))) L :=
      lic_limitingBelief_tendsto P (paperDP T) (paperDP_hworld T) _
    have hev : ∀ᶠ n in atTop, P n (paperPrimeDecompose (haltSentence a)) < 1 - 1 / ((k : ℝ) + 1) :=
      hconv.eventually_lt_const hLk
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    refine ⟨Nat.pair k (max N (f (Encodable.encode (haltSentence a)) k + 1)), ?_, ?_⟩
    · simp only [Nat.unpair_pair]
      exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
    · simp only [Nat.unpair_pair]
      have hn := hN (max N (f (Encodable.encode (haltSentence a)) k + 1)) (le_max_left _ _)
      rw [M.quote_exact] at hn
      have h2 : (1 : ℝ) - 1 / ((k : ℝ) + 1) = (k : ℝ) / ((k : ℝ) + 1) := by
        field_simp
        ring
      rw [h2] at hn
      have h3 := (lt_div_iff₀ hpos).mp hn
      have h4 : ((((k + 1 : ℕ) : ℚ) * M.quote (max N (f (Encodable.encode (haltSentence a)) k + 1))
          (Encodable.encode (paperPrimeDecompose (haltSentence a))) : ℚ) : ℝ) ≤
            (((k : ℕ) : ℚ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast h4

end Recoverer

/-! ## The contrast: without a modulus, the market itself is a computable approximant (findings F4;
audit r3 fidelity B1, probe `NoModulusRecoverable.lean` ported in repair round 3) -/

/-- **Without a modulus, every FAF inductor's limits are computably approximable — by the market's
own quote table.** For any inductor `P` over `DP` (with a consistent world at every stage) there IS
a computable table `g : ℕ → ℕ → ℚ` (day, sentence code) with `g n ⌜φ⌝ → limitingBelief P φ` for
every sentence `φ`: FAF's `ComputableMarket` field gives the table (`P n φ = quote n ⌜φ⌝` exactly)
and `lic_limitingBelief_tendsto` the convergence. So anson-029's modulus-free `𝓡(H) ⊊ 𝓢` is false
for every inductor FAF's criterion admits (at the computable level; the source's e.c. requirement by
time-padding, not machine-checked — F4), and the impossibility of T6.2
(`limit_non_recoverable_of_inductor`) rests on the computable *modulus*, not on uniformity.
Source: [[anson-inventory]] 029 (chat 11 L4590–4596, `𝓡(H) ⊊ 𝓢`); audit r3 fidelity B1
Kind: L
Fidelity: exact for the computable level (the source's `Ĥ` is e.c.)
Hyps: (a) -/
theorem exists_computable_modulusFree_approximant (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ g : ℕ → ℕ → ℚ, Computable (fun p : ℕ × ℕ => g p.1 p.2) ∧
      ∀ φ : Sentence, ConvergesTo (fun n => (g n (Encodable.encode φ) : ℝ)) (limitingBelief P φ) := by
  obtain ⟨M⟩ := hLI.marketComputable.nonemptyComputation
  refine ⟨M.quote, ?_, ?_⟩
  · have hfst : Computable fun z : ℕ => z.unpair.1 :=
      (Primrec.fst.comp Primrec.unpair).to_comp
    have hsnd : Computable fun z : ℕ => z.unpair.2 :=
      (Primrec.snd.comp Primrec.unpair).to_comp
    have h1 : Computable fun z : ℕ => M.quote z.unpair.1 z.unpair.2 :=
      marketComputation_quote_computable' M hfst hsnd
    have hpair : Computable fun p : ℕ × ℕ => Nat.pair p.1 p.2 :=
      Primrec₂.natPair.to_comp.comp Computable.fst Computable.snd
    exact (h1.comp hpair).of_eq fun p => by simp
  · intro φ
    have hfun : (fun n => (M.quote n (Encodable.encode φ) : ℝ)) = fun n => P n φ :=
      funext fun n => (M.quote_exact n φ).symm
    rw [hfun]
    exact lic_limitingBelief_tendsto P DP hworld φ

/-- The same at FAF's paper LIA over `paperDP 𝗜𝚺₁`, indexed by the code of the decomposition
`paperPrimeDecompose σ` — the exact shape T6.2's `limit_non_recoverable_ISigma1` forbids *with* a
modulus is, without one, satisfied by the market itself.
Source: [[anson-inventory]] 029; audit r3 fidelity B1
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem paper_modulusFree_approximant :
    ∃ g : ℕ → ℕ → ℚ, Computable (fun p : ℕ × ℕ => g p.1 p.2) ∧
      ∀ σ : ArithmeticSentence,
        ConvergesTo (fun n => (g n (Encodable.encode (paperPrimeDecompose σ)) : ℝ))
          (limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) (paperPrimeDecompose σ)) := by
  haveI : IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) :=
    LIA_is_logical_inductor _ (paperDP_computable _)
  obtain ⟨g, hg, hconv⟩ :=
    exists_computable_modulusFree_approximant (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁)
      (paperDP_hworld 𝗜𝚺₁)
  exact ⟨g, hg, fun σ => hconv _⟩

/-! ## Instances at `𝗜𝚺₁` and at the paper LIA (audit r2 N2) -/

/-- T6.2 at the mandate's `T := 𝗜𝚺₁`: no computable `f` uniformly approximates the limiting beliefs
of FAF's paper LIA over `paperDP 𝗜𝚺₁`. The section binders are inhabited by Foundation's instances
(`ISigma1_delta1Definable`, `WeakerThan.refl`, Σ₁-soundness of `𝗜𝚺₁` from `ℕ ⊧* 𝗜𝚺₁`).
Source: mandate T6.2 ("with `T := 𝗜𝚺₁`")
Kind: N+
Fidelity: exact
Hyps: none -/
theorem limit_non_recoverable_ISigma1 :
    ¬ ∃ f : ℕ → ℕ → ℚ, Computable (fun p : ℕ × ℕ => f p.1 p.2) ∧
      ∀ (σ : ArithmeticSentence) (k : ℕ),
        |(f (Encodable.encode σ) k : ℝ) -
            limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) (paperPrimeDecompose σ)| ≤ 1 / (k + 1) :=
  limit_non_recoverable 𝗜𝚺₁

/-- **T6.1 at the paper LIA** (the mandate's "T6.1 ship explicit histories"): for `li-quote-lane`'s
ledger conditioning family `ledgerSeq a e` (free of the projection atom, `atomFreeSentence_ledgerSeq`),
there is a rational `c ∈ (0,1)` such that the projection of FAF's paper LIA at `projAtomCode 0`
with weight `c` is an inductor over `paperDP 𝗜𝚺₁` (modulo the OPEN certificate (A), through
`u1_u2_inductor`), has the same `u`-free conditioned record, and a different limiting belief on
the atom. Inherits `u1_u2_inductor`'s Fidelity `weaker` (the record is `u`-free).
Source: mandate T6.1, Deliverables ("T6.1 ship explicit histories"); audit r2 fidelity N2 / adversarial 7
Kind: N+ (the hypothesis package is FAF's LIA, `paperDP_atomFree`, `paperDP_hworld`, `atomFreeSentence_ledgerSeq`; the inductor conjunct of the conclusion rests on (A))
Fidelity: weaker (as `u1_u2_inductor`)
Hyps: (a); the inductor conjunct rests on the OPEN rewriters -/
theorem paperU1U2 (a : ℕ → ℕ → ℚ) (e : ℕ → Cleanroom.Found.LiQuoteLane.PublicationSchedule) :
    ∃ c : ℚ, 0 < c ∧ c < 1 ∧
      IsLogicalInductor (project (liaHistory (paperDP 𝗜𝚺₁)) (projAtomCode 0) (fun _ => c))
        (paperDP 𝗜𝚺₁) ∧
      (∀ n φ, AtomFreeSentence (projAtomCode 0) φ →
        conditionedHistory (project (liaHistory (paperDP 𝗜𝚺₁)) (projAtomCode 0) (fun _ => c))
            (Cleanroom.Found.LiQuoteLane.ledgerSeq a e) n φ =
          conditionedHistory (liaHistory (paperDP 𝗜𝚺₁)) (Cleanroom.Found.LiQuoteLane.ledgerSeq a e) n φ) ∧
      limitingBelief (project (liaHistory (paperDP 𝗜𝚺₁)) (projAtomCode 0) (fun _ => c))
          (Formula.atom (projAtomCode 0)) ≠
        limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) (Formula.atom (projAtomCode 0)) :=
  haveI : IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) :=
    LIA_is_logical_inductor _ (paperDP_computable _)
  u1_u2_inductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁) (projAtomCode 0)
    (paperDP_atomFree 𝗜𝚺₁ 0) _ (atomFreeSentence_ledgerSeq 0 a e)

/-- At the pinned parameters `a ≡ 1/2`, same-day publication, the ledger conditioning family is a
genuine ledger literal (not `⊤`) at the position `⟨ledgerPayload 0 0 ⌜1/2⌝, 0⟩` — the one-line check
that `paperU1U2_half_sameDay`'s family is not trivial (audit r3 adversarial 3).
Source: none: infrastructure (`li-quote-lane`'s `ledgerSeq_eq_literal`)
Kind: L
Fidelity: n/a -/
theorem ledgerSeq_half_sameDay_literal :
    Cleanroom.Found.LiQuoteLane.ledgerSeq (fun _ _ => (1 / 2 : ℚ))
        (fun _ => Cleanroom.Found.LiQuoteLane.PublicationSchedule.sameDay)
        (Nat.pair (Cleanroom.Found.LiQuoteLane.ledgerPayload 0 0 (Encodable.encode (1 / 2 : ℚ))) 0) =
      literalOf (Cleanroom.Found.LiQuoteLane.ledgerEntry (fun _ _ => (1 / 2 : ℚ)) 0 0
        (Encodable.encode (1 / 2 : ℚ))) :=
  Cleanroom.Found.LiQuoteLane.ledgerSeq_eq_literal _ _ 0 0 _ 0 (by simp) (Nat.zero_le _)

/-- **`paperU1U2` pinned** (the mandate's "T6.1 ship explicit histories", audit r3 adversarial 3):
FAF's paper LIA over `paperDP 𝗜𝚺₁`, the atom `projAtomCode 0`, and the ledger family at the fixed
quote table `a ≡ 1/2` with same-day publication (`PublicationSchedule.sameDay`), which is a real
ledger literal at some position (`ledgerSeq_half_sameDay_literal`). Inherits `u1_u2_inductor`'s
Fidelity `weaker` and its (A)-dependence on the inductor conjunct.
Source: mandate T6.1, Deliverables; audit r3 adversarial 3
Kind: N+ (a pinned instance of the family `paperU1U2`; the inductor conjunct rests on (A))
Fidelity: weaker (as `u1_u2_inductor`)
Hyps: (a); the inductor conjunct rests on the OPEN rewriters -/
theorem paperU1U2_half_sameDay :
    ∃ c : ℚ, 0 < c ∧ c < 1 ∧
      IsLogicalInductor (project (liaHistory (paperDP 𝗜𝚺₁)) (projAtomCode 0) (fun _ => c))
        (paperDP 𝗜𝚺₁) ∧
      (∀ n φ, AtomFreeSentence (projAtomCode 0) φ →
        conditionedHistory (project (liaHistory (paperDP 𝗜𝚺₁)) (projAtomCode 0) (fun _ => c))
            (Cleanroom.Found.LiQuoteLane.ledgerSeq (fun _ _ => (1 / 2 : ℚ))
              (fun _ => Cleanroom.Found.LiQuoteLane.PublicationSchedule.sameDay)) n φ =
          conditionedHistory (liaHistory (paperDP 𝗜𝚺₁))
            (Cleanroom.Found.LiQuoteLane.ledgerSeq (fun _ _ => (1 / 2 : ℚ))
              (fun _ => Cleanroom.Found.LiQuoteLane.PublicationSchedule.sameDay)) n φ) ∧
      limitingBelief (project (liaHistory (paperDP 𝗜𝚺₁)) (projAtomCode 0) (fun _ => c))
          (Formula.atom (projAtomCode 0)) ≠
        limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) (Formula.atom (projAtomCode 0)) :=
  paperU1U2 (fun _ _ => (1 / 2 : ℚ)) (fun _ => Cleanroom.Found.LiQuoteLane.PublicationSchedule.sameDay)

/-! ## The coding fact, of record (not load-bearing since repair round 2) -/

/-- **OPEN, of record.** Numeral substitution is computable on sentence codes: for a fixed
one-variable arithmetic formula `φ`, `a ↦ Encodable.encode (φ/[‘↑a’])` is a computable function
`ℕ → ℕ`. Believed true (a primitive recursion over Foundation's `Nat.pair`-nested formula codes;
Foundation proves the arithmetised form `⌜φ/[a]⌝ = Bootstrapping.subst ?[numeral a] ⌜φ⌝` — here
`quote_numeralSubst` — and its Δ₁-definability, but states it as arithmetical definability, not
Mathlib `Computable`; a "total function with Σ₁ graph is `Computable`" bridge, absent from Mathlib
and Foundation, would finish it). **Nothing in this package rests on it since repair round 2**: T6.2
goes through the r.e. pullback `rePred_comp_numeralSubst` instead. Kept as an FAF/Foundation API
request; listed in section (D) of `li-projection-open.txt`.
Source: mandate T6.2 (the "numeral substitution computable on sentence codes" step); findings F11
Kind: OPEN
Fidelity: exact
Hyps: n/a -/
theorem numeralSubst_code_computable (φ : ArithmeticSemisentence 1) :
    Computable (fun a : ℕ => Encodable.encode (φ/[‘↑a’] : ArithmeticSentence)) := by
  sorry

end Cleanroom.Li.LiProjection
