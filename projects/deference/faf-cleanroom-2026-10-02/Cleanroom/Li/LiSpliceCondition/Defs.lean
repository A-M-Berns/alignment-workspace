import Cleanroom.Li.LiProjection.Subst
import Cleanroom.Li.LiProjection.Defs
import LogicalInduction.Properties.Conditioning
import LogicalInduction.Framework.Expectations

/-!
# `li-splice-condition` · Defs: definitions of record

Package `Cleanroom.Li.LiSpliceCondition` ([[li-splice-condition-mandate]]), file 1 of the layout.
The objects every later file states over:

* **Splice atoms** — family `4`, sub-family `1` of `bli-found`'s allocator (`spliceAtomCode`,
  `spliceAtom`; li-projection took sub-family `0`), with injectivity, distinctness from FAF's atoms
  and from the projection atoms, and freshness for cleanroom-free processes.
* **Splices** — `splice P₁ P₂ g` (day selector `g`), `paritySplice P₁ P₂` (odd days from `P₂`), and
  the **parity trader** `parityTrader φ M` (buy one share of `φ` on even days `≥ 2M`, sell it the
  next day; constant coefficients, price-free).
* **Criterion preservation** — `CriterionPreserving m DP` for a modification policy `m`.
* **Conditioning objects** — `condLeg`, `zeroOut`, `reprice` (E7's `ℙ⁰`, `ℙ^r`), `condExpect`
  (FAF's `LUV.expect` on FAF's `conditionedHistory`), and `UndecidedLUV`.
* **Refreezing** — `staleHistory P g`.

Every price-valued definition says what it does at its junk points. Nothing here reads another
inductor's ledger: every two-market statement of the package is one-way (plan §0.4 rule 1).
-/

namespace Cleanroom.Li.LiSpliceCondition

open LogicalInduction LO.Propositional Cleanroom.Li.LiProjection Cleanroom.Bli.BliFound

/-! ## Splice atoms (family 4, sub-family 1) -/

/-- The code of the `k`-th splice atom: family `4`, payload `Nat.pair 0 (Nat.pair 1 k)` (day `0`
first by the registry rule, then sub-family `1`, then the index).
Source: mandate header ("You take sub-family `1`"); `Cleanroom/Bli/BliFound/Tags.lean` registry
Kind: D
Fidelity: n/a -/
def spliceAtomCode (k : ℕ) : ℕ := freshAtomCode 4 (Nat.pair 0 (Nat.pair 1 k))

/-- The `k`-th splice atom as a sentence.
Source: mandate header
Kind: D
Fidelity: n/a -/
def spliceAtom (k : ℕ) : Sentence := Formula.atom (spliceAtomCode k)

/-- `spliceAtom k` is `bli-found`'s `freshAtom` at the sub-family-`1` payload.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceAtom_eq_freshAtom (k : ℕ) : spliceAtom k = freshAtom 4 (Nat.pair 0 (Nat.pair 1 k)) :=
  rfl

/-- Splice-atom codes are injective in the index.
Source: mandate header ("injectivity")
Kind: L
Fidelity: n/a -/
lemma spliceAtomCode_injective : Function.Injective spliceAtomCode := by
  intro j k h
  have h1 := (freshAtomCode_inj.mp h).2
  have h2 := (Nat.pair_eq_pair.mp h1).2
  exact (Nat.pair_eq_pair.mp h2).2

/-- A splice atom carries a tag `> 8`, so it is none of FAF's own atoms (FAF's tags are `< 9`).
Source: mandate header ("`≠` FAF atoms"); `bli-found` `freshAtomCode_tag_gt`
Kind: L
Fidelity: n/a -/
lemma spliceAtom_ne_faf (k : ℕ) : 8 < (spliceAtomCode k).unpair.1 :=
  freshAtomCode_tag_gt 4 _

/-- A splice atom is never a projection atom of li-projection (sub-family `1` versus `0`).
Source: mandate header ("`≠ projAtomCode j`")
Kind: L
Fidelity: n/a -/
lemma spliceAtomCode_ne_projAtomCode (k j : ℕ) : spliceAtomCode k ≠ projAtomCode j := by
  intro h
  have h1 := (freshAtomCode_inj.mp h).2
  have h2 := (Nat.pair_eq_pair.mp h1).2
  have h3 := (Nat.pair_eq_pair.mp h2).1
  omega

/-- A cleanroom-free sentence (every atom in FAF's own vocabulary) is free of every splice atom.
Source: none: infrastructure (the analogue of li-projection's `atomFreeSentence_of_cleanroomFree`)
Kind: L
Fidelity: n/a -/
lemma atomFreeSentence_splice_of_cleanroomFree {φ : Sentence} (h : CleanroomFreeSentence φ)
    (k : ℕ) : AtomFreeSentence (spliceAtomCode k) φ :=
  h.freshAtomCode_notMem 4 _

/-- A cleanroom-free process (e.g. `paperDP T`, by `bli-found`'s `paperDP_cleanroomFree`) is free
of every splice atom. li-projection's `atomFreeProcess_of_cleanroomFree` is pinned to
`projAtomCode`; this is its one-line analogue at the sub-family-`1` codes.
Source: mandate header ("if it is pinned to `projAtomCode`, prove the one-line analogue")
Kind: L
Fidelity: exact -/
lemma atomFreeProcess_splice_of_cleanroomFree {DP : DeductiveProcess} (h : CleanroomFreeProcess DP)
    (k : ℕ) : AtomFreeProcess (spliceAtomCode k) DP :=
  fun n φ hφ => atomFreeSentence_splice_of_cleanroomFree (h n φ hφ) k

/-! ## Splices and the parity trader -/

/-- **The splice** of two histories along a day selector: on day `n` the prices are `P₂`'s when
`g n` and `P₁`'s otherwise. Covers the source's adaptive alternation (`g` may be anything; nothing
here asks it to be computable — that enters only in `computableMarket_splice`).
Source: [[corr-wf14-inventory]] 047 (`selection.md` R1.4, "any process that takes value `ℙ¹_n(φ)` infinitely often and `ℙ²_n(φ)` infinitely often")
Kind: D
Fidelity: exact -/
noncomputable def splice (P₁ P₂ : History) (g : ℕ → Bool) : History :=
  fun n φ => if g n then P₂ n φ else P₁ n φ

/-- The daily alternation `S_n = P^{1 + (n mod 2)}_n`: even days from `P₁`, odd days from `P₂`.
Source: [[corr-wf13-inventory]] 062 (`positive/li.md` I14.4, "a daily splice of two inductors")
Kind: D
Fidelity: exact -/
noncomputable def paritySplice (P₁ P₂ : History) : History :=
  splice P₁ P₂ (fun n => n % 2 = 1)

/-- `splice_apply`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma splice_apply (P₁ P₂ : History) (g : ℕ → Bool) (n : ℕ) (φ : Sentence) :
    splice P₁ P₂ g n φ = if g n then P₂ n φ else P₁ n φ := rfl

/-- On an even day the parity splice is `P₁`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma paritySplice_even (P₁ P₂ : History) (k : ℕ) (φ : Sentence) :
    paritySplice P₁ P₂ (2 * k) φ = P₁ (2 * k) φ := by
  simp [paritySplice, splice, Nat.mul_mod_right]

/-- On an odd day the parity splice is `P₂`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma paritySplice_odd (P₁ P₂ : History) (k : ℕ) (φ : Sentence) :
    paritySplice P₁ P₂ (2 * k + 1) φ = P₂ (2 * k + 1) φ := by
  simp [paritySplice, splice, Nat.add_mod, Nat.mul_mod_right]

/-- The parity trader's day-`n` coefficient on `φ`: `0` before day `2M`, `s` on even days, `−s` on
odd days from day `2M` on (`s = 1`: buy on even days, sell on odd; `s = −1`: the reverse, for a
limit gap of the other sign). Rational, so that it sits inside `EF.const`.
Source: mandate `Defs` table (`parityTrader`); the start day is `N = 2M` (an even day, so that the
first trade opens a pair and every later day completes or opens one)
Kind: D
Fidelity: variant: the start day is parametrised as `2M` rather than an arbitrary `N`, and the
orientation `s` is a parameter (the mandate's "state both or use `|L₁ − L₂|`") -/
def parityCoeff (s : ℚ) (M n : ℕ) : ℚ := if n < 2 * M then 0 else if n % 2 = 0 then s else -s

/-- **The parity trader**: buy `s` shares of `φ` on each even day `≥ 2M`, sell them the next day
(`s ∈ {1, −1}` in every use). One trade per day with a constant coefficient (price-free), so it
holds at most one share and its efficiency certificate is FAF's single-trade constructor on a
three-way dispatch by the day (`parityTrader_ec`, `Splice.lean`). This is the LI paper's
buy-low/sell-high trader with the "low"/"high" days fixed by parity instead of read off the price.
Source: [[corr-wf14-inventory]] 047–048 (`selection.md` R1.4 "buy … sell back", R1.5 "buy one share on even days, sell on odd days"); mandate T1.3
Kind: D
Fidelity: exact -/
def parityTrader (φ : Sentence) (s : ℚ) (M : ℕ) : Trader where
  strat n := { trades := [(EF.const (parityCoeff s M n), φ)], rank_le := by simp }

/-! ## Criterion preservation -/

/-- **Criterion preservation** of a modification policy `m : History → History` over `DP`: every
inductor over `DP` is sent to an inductor over `DP`. The note's legitimacy definition of record
for a *pushed* process (I5.7). Nothing here is called `Legitimate`. Its immediate consequence in
the note — "`cee`/`ccee` hold for the pushed process" — is the instance
`[IsLogicalInductor (m P) DP]` of FAF's `lic_expected_future_expectations`, and needs no theorem.
Source: [[corr-wf13-inventory]] 069 (`positive/li.md` I5.7, criterion-preservation); mandate T2.1
Kind: D
Fidelity: exact -/
def CriterionPreserving (m : History → History) (DP : DeductiveProcess) : Prop :=
  ∀ P : History, IsLogicalInductor P DP → IsLogicalInductor (m P) DP

/-- The finite-patch policy `P ↦ patch P S t` (li-projection's `patch`).
Source: mandate T2.2
Kind: D
Fidelity: exact -/
noncomputable def patchPolicy (S : Finset (ℕ × Sentence)) (t : ℕ → Sentence → ℚ) :
    History → History :=
  fun P => patch P S t

/-! ## Conditioning on a refuted sentence: the two perturbed markets -/

/-- The first conjunct of `χ` when `χ = φ ⋏ ψ` with `φ ∈ Φ`, else `none`. Recognises the
re-priced sentences of E7 syntactically (a `Formula.and` whose right conjunct is `ψ`).
Source: [[corr-legit-neg-inventory]] 060–061 (E7 (i)–(ii), "`φ ∧ ψ` for `φ ∈ Φ`")
Kind: D
Fidelity: exact -/
def condLeg (ψ : Sentence) (Φ : Finset Sentence) : Sentence → Option Sentence
  | .and φ ψ' => if ψ' = ψ ∧ φ ∈ Φ then some φ else none
  | _ => none

/-- `condLeg` at a conjunction with `φ ∈ Φ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condLeg_and {ψ : Sentence} {Φ : Finset Sentence} {φ : Sentence} (hφ : φ ∈ Φ) :
    condLeg ψ Φ (φ ⋏ ψ) = some φ := by
  simp [condLeg, hφ]

/-- `condLeg` is `some φ` exactly at `φ ⋏ ψ` with `φ ∈ Φ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condLeg_eq_some_iff {ψ : Sentence} {Φ : Finset Sentence} {χ φ : Sentence} :
    condLeg ψ Φ χ = some φ ↔ χ = φ ⋏ ψ ∧ φ ∈ Φ := by
  constructor
  · intro h
    cases χ with
    | and a b =>
        simp only [condLeg] at h
        split_ifs at h with hab
        · cases h; exact ⟨by rw [hab.1]; rfl, hab.2⟩
    | atom _ => simp [condLeg] at h
    | falsum => simp [condLeg] at h
    | or _ _ => simp [condLeg] at h
    | imp _ _ => simp [condLeg] at h
  · rintro ⟨rfl, hφ⟩
    exact condLeg_and hφ

/-- **E7's `ℙ⁰`**: `P` except that `ψ` and every `φ ⋏ ψ` (`φ ∈ Φ`) are priced `0` on days `≥ N`.
Days `< N` are untouched. `Φ` is a finite set so that the market stays computable from `P`'s
table (`computableMarket_zeroOut`); the certificate of the translated trader is the OPEN fact
of `Open.lean`, not a hypothesis of this definition.
Source: [[corr-legit-neg-inventory]] 060 (E7 (i), the convention horn)
Kind: D
Fidelity: variant: `Φ` finite (the source has `Φ` polynomial-time decidable) -/
noncomputable def zeroOut (P : History) (ψ : Sentence) (Φ : Finset Sentence) (N : ℕ) : History :=
  fun n χ => if N ≤ n ∧ (χ = ψ ∨ (condLeg ψ Φ χ).isSome) then 0 else P n χ

/-- **E7's `ℙ^r`**: `P` except that `φ ⋏ ψ` (`φ ∈ Φ`) is priced `r φ n · P n ψ`. Every other
sentence, `ψ` included, keeps `P`'s price. No division anywhere: the conditional-quote identity
`P^r_n(φ | ψ) = r φ n` is a *theorem* under `0 < P n ψ` and `r φ n < 1` (`conditionedHistory_reprice`),
never part of the definition.
Source: [[corr-legit-neg-inventory]] 061 (E7 (ii), the free horn)
Kind: D
Fidelity: variant: `Φ` finite -/
noncomputable def reprice (P : History) (ψ : Sentence) (Φ : Finset Sentence)
    (r : Sentence → ℕ → ℚ) : History :=
  fun n χ => match condLeg ψ Φ χ with
    | some φ => (r φ n : ℝ) * P n ψ
    | none => P n χ

/-- `reprice` at a re-priced sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma reprice_and (P : History) (ψ : Sentence) (Φ : Finset Sentence) (r : Sentence → ℕ → ℚ)
    (n : ℕ) {φ : Sentence} (hφ : φ ∈ Φ) :
    reprice P ψ Φ r n (φ ⋏ ψ) = (r φ n : ℝ) * P n ψ := by
  simp [reprice, condLeg_and hφ]

/-- `reprice` off the re-priced sentences.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma reprice_of_none (P : History) (ψ : Sentence) (Φ : Finset Sentence) (r : Sentence → ℕ → ℚ)
    (n : ℕ) {χ : Sentence} (h : condLeg ψ Φ χ = none) :
    reprice P ψ Φ r n χ = P n χ := by
  simp [reprice, h]

/-- **The conditional expectation of record**: FAF's `LUV.expect` on FAF's `conditionedHistory`
at the fixed condition `ψ` — i.e. the E7 recipe
`𝔼_n(X | ψ) = (1/(n+1)) Σ_{i ≤ n} P_n(⌜X > i/(n+1)⌝ | ψ)` with FAF's capped conditional quote
(`conditionalQuote`, junk value `1` when `P_n(ψ) = 0`). An `abbrev`, not a new sum.
Source: [[corr-legit-neg-inventory]] 060 ("`𝔼_n(X | ψ) = Σ_{i<n} (1/n)·P_n(⌜X > i/n⌝ | ψ)`"); FAF `Framework/Expectations.lean` `def:e`
Kind: D
Fidelity: exact (precision `n+1` on Lean day `n`, FAF's day convention) -/
noncomputable abbrev condExpect (P : History) (ψ : Sentence) (X : LUV) (n : ℕ) : ℝ :=
  X.expect (conditionedHistory P (fun _ => ψ)) n

/-- **An undecided LUV**: at every threshold `r ∈ (0,1)` and every stage `n`, both verdicts on
`⌜X > r⌝` are plausible (a stage-consistent world holding it, another refuting it) — the stagewise
semantic form of "any hypothesis about utility is consistent under the axioms", and exactly the
premise shape of FAF's `lic_nonDogmatism`/`lic_nonDogmatism_dual`. The thresholds are restricted
to the open unit interval: for a `[0,1]`-LUV, `⌜X > r⌝` at `r < 0` (resp. `r ≥ 1`) is held (resp.
refuted) by every world valuing `X` (`PCWorld.ValuesAt`), so the mandate's `∀ r` form would be
incompatible with FAF's `hval` on any valued world (findings).
Source: [[corr-core-inventory]] 034(i) (BLI paste l. 45, "undecidable, so that any hypothesis about utility is consistent under the axioms")
Kind: D
Fidelity: variant: stagewise, thresholds in `(0,1)` (the source speaks of consistency with the axioms; FAF's stages are its finite approximants) -/
def UndecidedLUV (DP : DeductiveProcess) (X : LUV) : Prop :=
  ∀ (r : ℚ), 0 < r → r < 1 → ∀ (n : ℕ),
    (∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds (X.gt r)) ∧
    (∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ ¬ v.Holds (X.gt r))

/-! ## Refreezing -/

/-- **The stale history** `n ↦ P (g n)`: the belief state consulted on day `n` is `P`'s state on
the refreeze day `g n`. Monotonicity, `g n ≤ n` and `g → ∞` are hypotheses of the theorems, not
of the definition. ATTRIBUTION-UNVETTED reading of Soto's "re-freeze infinitely often".
Source: [[bli-soto-b-inventory]] 016(iii) (Soto PDF 15 p. 4)
Kind: D
Fidelity: variant: the reading of record -/
noncomputable def staleHistory (P : History) (g : ℕ → ℕ) : History :=
  fun n => P (g n)

end Cleanroom.Li.LiSpliceCondition
