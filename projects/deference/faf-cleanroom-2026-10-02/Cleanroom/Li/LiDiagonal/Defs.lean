import Cleanroom.Found.LiQuoteLane.Defs
import LogicalInduction.Properties.Introspection
import LogicalInduction.Properties.SelfTrust
import LogicalInduction.Properties.Calibration

/-!
# `li-diagonal`: definitions of record

The definitions module of the package `Cleanroom.Li.LiDiagonal` ([[li-diagonal-mandate]]). Only
definitions and the unfolding lemmas that pin them live here; theorem files import this one.

Three diagonals recur in the corpus, and this package states them over FAF's objects:

* **FAF's same-day diagonal** `χ^p_n ↔ (ℙ_n(χ^p_n) < p)` is FAF's `ParadoxResistanceQuote`
  (`Properties/Introspection.lean`) and its Kleene instance
  `parameterizedDiagonalQuoteCodeOfMarket` (`Construction/Quotation/Packages.lean`). This
  package defines **no** new diagonal of that kind.
* **The deferred liar** `χ_n ↔ (ℙ_{f(n)}(χ_n) < p)` of [[weak-endorsement-deference-model]] §2.1 is
  the reindexing `defDiag ψ f n := ψ (f n)` of a same-day diagonal `ψ`: the sentence `ψ (f n)` is
  true iff its own day-`f n` price is below `p`, which is exactly what the deferred liar asks of
  `χ_n`. **Never a new fixed point** (T5a).
* **The cross-process family** `g_n ↔ (a_n ≤ ½)` of the faithful-acceleration chats is the negation
  of one ledger atom of `li-quote-lane`: `gDiag n := ∼⌜α_{0,n} > ½⌝`. Ties at exactly `½` make
  `g_n` true — the ledger's strict `>` polarity (`li-quote-lane` disclosure (β)) *is* the chat's
  unavailable rounding convention.

**Scope tags** (plan §0.4 rule 1): `defDiag`, `side`, `AgentCoupling`,
`VariedParadoxResistanceQuote` are single-market; `gDiag` is one-way (it lives in the reader's
language); `DiagonalPair` is the **two-way** object — its inhabitation is `li-coupled-pair`'s open
row, and every headline stated over it is `partial: over the OPEN pair`.

**Naming discipline** (plan §0.4 rule 10): nothing here is called `ParadoxResistanceQuote`,
`PGenerableWeighting`, `DeferralPatient` or `TotalTrust`.
-/

namespace Cleanroom.Li.LiDiagonal

open LogicalInduction LO.Propositional Cleanroom.Found.LiQuoteLane
open Filter Topology

/-! ## A. The deferred liar as a reindexing -/

/-- **The deferred liar** `χ_n := ψ (f n)`: the day-`f n` member of a same-day diagonal family
`ψ`, read on day `n`. With `ψ` FAF's diagonal of `(market, T, p)`, `defDiag ψ f n` holds in
every completed world iff `P (f n) (defDiag ψ f n) < p` (`defDiag_reflected`, `Deferred.lean`).
Scope: single-market; threshold `p` and deferral `f` are those of `ψ` and of the reindexing.
Source: [[weak-endorsement-deference-model]] §2.1 (trust-lab-023); [[li-diagonal-mandate]] § Definitions of record
Kind: D
Fidelity: exact — the note's `χ_n ↔ (ℙ_{f(n)}(χ_n) < ½)` is this family at `p = ½`; the note treats it as a new fixed point, it is a reindexing (finding, presentation)
Hyps: n/a -/
def defDiag (ψ : ℕ → Sentence) (f : DeferralFunction) : ℕ → Sentence :=
  fun n => ψ (f n)

/-- `defDiag_apply`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma defDiag_apply (ψ : ℕ → Sentence) (f : DeferralFunction) (n : ℕ) :
    defDiag ψ f n = ψ (f n) := rfl

/-- **The truth stream of a diagonal**: `1` on the days the day-`n` price of `ψ n` is below `p`,
`0` otherwise. Over a `ParadoxResistanceQuote` this is the completed-theory payout of
`q.sentence n` (`diagonal_reflected`), i.e. a `TheoryTruth` (T4).
Scope: single-market.
Source: [[lean-deference-inventory]] 050 (the "truth" the pointwise face is measured against)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def diagTruth (P : History) (ψ : ℕ → Sentence) (p : ℚ) (n : ℕ) : ℝ :=
  if P n (ψ n) < (p : ℝ) then 1 else 0

/-! ## B. The cross-process family over the ledger -/

/-- **The cross-process family `g_n`** of record: `g_n := ∼⌜α_{0,n} > ½⌝`, the negation of the
ledger atom of item `0`, day `n`, threshold `½` (`li-quote-lane`'s `ledgerLuv`). In every world
consistent with the ledger process past the publication stage, `g_n` holds iff the published
`a 0 n ≤ ½` (`gDiag_decided`, `Family.lean`): ties at exactly `½` make `g_n` *true*, the ledger's
strict `>` polarity. This is the only sentence family this package defines over the ledger.
Scope: one-way (in the reader's language; what `A` quotes about it is `DiagonalPair`'s business).
Source: [[lean-deference-2-inventory]] 006 (`g_n ≡ ¬β_{n,k*(n)}`); FA-critique chat msg 21 (`g_n`)
Kind: D
Fidelity: exact, with `li-quote-lane`'s disclosures (α) code-bounded thresholds and (β) strict polarity (ties → true)
Hyps: n/a -/
def gDiag (n : ℕ) : Sentence := ∼ ((ledgerLuv 0 n).gt (1 / 2))

/-- `gDiag_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gDiag_eq (n : ℕ) : gDiag n = ∼ ((ledgerLuv 0 n).gt (1 / 2)) := rfl

/-- **The settled side** `s_n := 𝟙[a_n ≤ ½]` of a published table (item `0`): the real-valued
truth of `g_n` as a function of the number `A` published.
Scope: one-way.
Source: [[lean-deference-2-inventory]] 007 (the side `s_n`); [[lean-deference-inventory]] 048
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def side (a : ℕ → ℚ) (n : ℕ) : ℝ := if a n ≤ 1 / 2 then 1 else 0

/-- `side_mem`: the side is `0` or `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma side_eq_zero_or_one (a : ℕ → ℚ) (n : ℕ) : side a n = 0 ∨ side a n = 1 := by
  unfold side; split_ifs <;> simp

/-- `side_eq_one_iff`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma side_eq_one_iff (a : ℕ → ℚ) (n : ℕ) : side a n = 1 ↔ a n ≤ 1 / 2 := by
  unfold side
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h0 => absurd h0 zero_ne_one, fun h1 => absurd h1 h⟩

/-- `side_eq_zero_iff`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma side_eq_zero_iff (a : ℕ → ℚ) (n : ℕ) : side a n = 0 ↔ 1 / 2 < a n := by
  unfold side
  split_ifs with h
  · exact ⟨fun h1 => absurd h1 one_ne_zero, fun hlt => absurd h (not_le.mpr hlt)⟩
  · exact ⟨fun _ => not_le.mp h, fun _ => rfl⟩

/-! ## C. The two-way object -/

/-- **The diagonal pair**: the two-way object every cross-process headline of this package is
stated over. `pair` is `li-quote-lane`'s one-way pair (`H` reads `A`'s published table through
the ledger); `cross` is `li-quote-lane`'s `CrossQuotePackage` saying `A`'s LUV family `Y n` is
determined, in `A`'s completed theory, at `H`'s realized day-`f n` expectation of the indicator
of `g_n` (`A` reads `H`); `quoted_eq` ties the published number to `A`'s price of the median
threshold `⌜Y_n > ½⌝`. **Disclosure:** the published number is `A`'s *price* of `⌜Y_n > ½⌝`,
not `A`'s *expectation* of `Y_n` (fidelity `variant`; the two agree once `Y_n` is determined
within `¼` of `{0,1}`, which `forcingA`'s `htrack` supplies). **Its inhabitation is
`li-coupled-pair`'s OPEN**: this is a structure, not a theorem; `∃ D : DiagonalPair f` is stated
nowhere in this package. Every headline over it carries `cross.reflected` as hypothesis (c)
(the Σ₁-completeness of `Γ_A` about `H`'s machine) and `hworldA` for `A`'s process.
Scope: two-way (`partial: over the OPEN pair`).
Source: [[faithful-acceleration]] §3–4 (root-fa-018, the (A2)/(A3) assumptions); [[lean-deference-inventory]] 048; [[li-diagonal-mandate]] § Definitions of record
Kind: D
Fidelity: variant: price of the median threshold in place of the expectation (disclosed above)
Hyps: (c) `cross.reflected` for every headline stated over it -/
structure DiagonalPair (f : DeferralFunction) where
  /-- The one-way pair: `H` reads `A`'s table through the ledger. -/
  pair : OneWayPair
  /-- `A`'s quote LUV family: `Y n` is `A`'s rendering of `𝔼^H_{f(n)}(𝟙 g_n)`. -/
  Y : ℕ → LUV
  /-- `A` reads `H`: `Y n` is determined in `A`'s completed theory at `H`'s realized
  day-`f n` expectation of `𝟙 g_n`. -/
  cross : CrossQuotePackage pair.H pair.DPA f (fun n => LUV.indicatorOf (gDiag n)) Y
  /-- `A`'s process has a consistent world at every stage. -/
  hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (pair.DPA.D n)
  /-- The published item `0` on day `n` is `A`'s price of the median threshold `⌜Y_n > ½⌝`. -/
  quoted_eq : ∀ n, pair.quoted 0 n = (Y n).gt (1 / 2)

/-- The published number of a diagonal pair is `A`'s price of `⌜Y_n > ½⌝`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma DiagonalPair.a_eq_price {f : DeferralFunction} (D : DiagonalPair f) (n : ℕ) :
    (D.pair.a 0 n : ℝ) = D.pair.A n ((D.Y n).gt (1 / 2)) := by
  rw [D.pair.a_eq 0 n, D.quoted_eq n]

/-! ## D. The agent coupling (bli-soto) -/

/-- **The agent–inductor coupling** of bli-soto-a-066: an environment in which `D n` is the
sentence "the agent defects on round `n`", the agent defects iff the inductor's day-`n` price
of `D n` is below the threshold `p n` (`reflected`, in every completed world of `DP`), and the
realized play is fed to the process on the next day (`decided_by`). `decided_by` is the
bounded-refutation-delay clause the source's "never loses" silently needs (K7): FAF's
`ParadoxResistanceQuote` gives `reflected` but nothing like `decided_by`, whose delay over
the paper's own `paperDP` is uncontrolled.
Scope: single-market; threshold family `p`.
Source: [[bli-soto-a-inventory]] 066 ("`A` defects iff `1/P_n(D_n) > 2n`"), 067; [[bli-soto-b-inventory]] 036
Kind: D
Fidelity: variant: the source's `1/P_n(D_n) > 2n` is `P_n(D_n) < 1/(2n)`, the instance `p n := 1/(2(n+1))`
Hyps: (c) the whole structure is the environment's design, not an LI fact. Note (audit r1 N10): `reflected` is implied by `decided_by` (the decided literal is in the process by day `n+1`, so every completed-theory world agrees with the price test); it is kept as a named field for readability, not as an extra assumption -/
structure AgentCoupling (P : History) (DP : DeductiveProcess) (D : ℕ → Sentence)
    (p : ℕ → ℚ) : Prop where
  /-- The defection sentences are e.c. -/
  codes : MachineSentenceCodes D
  /-- The agent defects iff its day-`n` price is below the threshold. -/
  reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    (v.Holds (D n) ↔ P n (D n) < (p n : ℝ))
  /-- The realized play is in the process by the next day. -/
  decided_by : ∀ n, (if P n (D n) < (p n : ℝ) then D n else ∼ (D n)) ∈ DP.D (n + 1)

/-! ## E. The varied-threshold paradox-resistance package (T8c) -/

/-- **FAF's `ParadoxResistanceQuote` with a day-varying threshold** `p : ℕ → ℚ`, generable from
the market (`hp : GeneratedRatFeature P p pFeature`), the two affine certificates stated at
`pFeature`'s denotation `p n`. The varied diagonal `χ_n ↔ (ℙ_n(χ_n) < p_n)` of bli-soto-b-036's
open question. Inhabitation on FAF's Kleene construction is the stretch target (`Varied.lean`).
Scope: single-market; threshold family `p`.
Source: [[bli-soto-b-inventory]] 036; FAF `ParadoxResistanceQuote` (`Properties/Introspection.lean`)
Kind: D
Fidelity: variant: `ParadoxResistanceQuote` with `p : ℚ` replaced by a generable `p : ℕ → ℚ`
Hyps: n/a -/
structure VariedParadoxResistanceQuote (P : History) (DP : DeductiveProcess)
    (p : ℕ → ℚ) (pFeature : ℕ → EF) where
  /-- The diagonal family. -/
  sentence : ℕ → Sentence
  /-- It is e.c. -/
  sentence_codes : MachineSentenceCodes sentence
  /-- The ramp width. -/
  width : ℕ → ℚ
  /-- Positive. -/
  width_pos : ∀ n, 0 < width n
  /-- Vanishing. -/
  width_tendsto_zero : Tendsto (fun n => (width n : ℝ)) atTop (𝓝 0)
  /-- The threshold family is generable: `pFeature n` denotes `p n` at the market. -/
  hp : GeneratedRatFeature P p pFeature
  /-- The diagonal reflection at the day-`n` threshold. -/
  diagonal_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    (v.Holds (sentence n) ↔ P n (sentence n) < (p n : ℝ))
  /-- The lower affine certificate at threshold `p n`. -/
  lower_affine : CompletedAffineQuoteEq P DP (fun n =>
    ctsInd (width n) (p n : ℝ) (P n (sentence n)) * (1 - P n (sentence n)))
  /-- The upper affine certificate at threshold `p n`. -/
  upper_affine : CompletedAffineQuoteEq P DP (fun n =>
    ctsInd (width n) (P n (sentence n)) (p n : ℝ) * P n (sentence n))

end Cleanroom.Li.LiDiagonal
