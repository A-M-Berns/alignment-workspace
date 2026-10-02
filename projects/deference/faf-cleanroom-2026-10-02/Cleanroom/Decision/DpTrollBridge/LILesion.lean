/-
  The Löbian lesion at the level of a logical inductor: what is provable now, and the OPEN
  statements.

  Targets 10 and 11 of [[dp-troll-bridge-mandate]]. This is the only file of the package that
  imports `LogicalInduction`; everything else lives in GL.

  - `li_lesion_alpha` (kind L): the LI form of (α) for the lesion — if `cross n 🡒 incon n`
    holds in every world consistent with the completed deductive process (this is where
    "T ⊢ Cross_n → □⊥" enters, at the paper's Θ-completeness quantifier), the inductor's
    price of it tends to `1` (`lic_provind_true`, instantiated).
  - `li_lesion_conj` (kind C; was OPEN in round 0): the coherence step `P n (incon ⋏ cross)
    − P n cross → 0` under the same hypothesis, through FAF's affine coherence on the
    two-share family `[incon ⋏ cross] − [cross]` (`lesionAffine`), whose value is `0` in every
    completed-theory world where the lesion holds.
  - `li_lesion_conditional` (kind P): from the coherence step, the capped conditional quote
    `P_n(incon | cross)` tends to `1` **on the days where `P n (cross n) ≥ ε`**. The `ε`-clause
    is the doc's non-dogmatism `P(Cross) > 0` and is where P11-3′'s obstruction lives: when
    `P n (cross n) → 0`, `conditionalQuote` returns its junk value `1` and the unrestricted
    conditional statement would be vacuous. Holds for any history (no inductor needed).
  - `li_lesion_conditional_of_theory` (kind C): the target-10 composite, (α)-hypothesis →
    coherence → `ε`-conditional, with no hypothesis left open.
  - `li_responsive_lesion_open` (OPEN): the LI-based responsive agent satisfies the lesion for
    all large `n` — the research question of dp-sl-2-034; `responsive_lesion_day_iff` shows
    that under its own hypotheses this is "the agent eventually provably stays".
  - `flower_liminf_open` (OPEN): Soto's flower obstruction, `liminf P n (S n) ≥ p`,
    unconditionally; `FlowerLI.lean` proves it conditional on the quotation portfolio
    (`flower_liminf_of_portfolio`).
-/

import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Properties.Conditioning

open LO
open LogicalInduction
open scoped LogicalInduction
open Filter Topology

namespace Cleanroom.Decision.DpTrollBridge

/-! ## Boolean-world plumbing -/

/-- `v.Holds (φ 🡒 ψ)` is the material implication of the two `Holds` (Boolean valuation).
Source: none: infrastructure (FAF `PCWorld.Holds` is `Formula.Boolean.val`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma holds_imp (v : PCWorld) (φ ψ : Sentence) :
    v.Holds (φ 🡒 ψ) ↔ (v.Holds φ → v.Holds ψ) := by
  simp [PCWorld.Holds, LO.Propositional.Formula.Boolean.val]

/-! ## Target 10: what is provable now -/

/-- **The LI form of (α) for the lesion.** If the lesion sentence `cross n 🡒 incon n` holds
in every world consistent with the completed deductive process (the paper's Θ-completeness
reading of "T ⊢ Cross_n → □⊥"), and the sequence is machine-codeable, then the inductor's
price of the lesion sentence tends to `1`. This is `lic_provind_true` at the sentence
`cross n 🡒 incon n`, nothing chained; it is the first step of Lemma 8 at the LI level, and
it is asymptotic where the doc's (α) is exact.
Source: [[dp-sl-2-inventory]] 034; [[two-lesions-doc-2026-09-18]] §7 (α); [[dp-troll-bridge-mandate]] target 10
Kind: L
Fidelity: variant: (α) holds only in the limit for an inductor; "T proves" is rendered as "holds in every completed-theory world"
Hyps: (a) none beyond FAF's `IsLogicalInductor`; (c) `hthm` is the semantic rendering of "T ⊢ cross n → □⊥" -/
theorem li_lesion_alpha (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (cross incon : ℕ → Sentence)
    (hcodes : MachineSentenceCodes (fun n => cross n 🡒 incon n))
    (hthm : ∀ n, ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (cross n 🡒 incon n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (cross n 🡒 incon n)) ≈ₙ fun _ => 1 :=
  lic_provind_true P DP _ hcodes hthm hworld

/-- The two-share affine combination `[incon n ⋏ cross n] − [cross n]` (constant `0`).
Source: none: infrastructure (the coherence step of dp-sl-2-034)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def lesionAffine (cross incon : ℕ → Sentence) (n : ℕ) : AffineCombination where
  const := .const 0
  terms := [(.const 1, incon n ⋏ cross n), (.const (-1), cross n)]

/-- Price of `lesionAffine` on day `m`: `P m (incon n ⋏ cross n) − P m (cross n)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma lesionAffine_price (cross incon : ℕ → Sentence) (P : History) (n m : ℕ) :
    (lesionAffine cross incon n).price P m = P m (incon n ⋏ cross n) - P m (cross n) := by
  simp only [lesionAffine, AffineCombination.price, AffineCombination.value, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, EF.denote_const]
  push_cast
  ring

/-- Value of `lesionAffine` under a valuation `w`: `w (incon n ⋏ cross n) − w (cross n)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma lesionAffine_value (cross incon : ℕ → Sentence) (P : History) (n : ℕ) (w : Valuation) :
    (lesionAffine cross incon n).value P w = w (incon n ⋏ cross n) - w (cross n) := by
  simp only [lesionAffine, AffineCombination.value, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, EF.denote_const]
  push_cast
  ring

/-- Magnitude of `lesionAffine`: `|1| + |−1| = 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma lesionAffine_magnitude (cross incon : ℕ → Sentence) (P : History) (n : ℕ) :
    (lesionAffine cross incon n).magnitude P = 2 := by
  simp only [lesionAffine, AffineCombination.magnitude, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, EF.denote_const]
  push_cast
  norm_num

/-- `lesionAffine` is a polynomial affine family (FAF's `PolySequence`, `def:ec`) whenever
`cross` and `incon` are machine-codeable: two terms per day, coefficients `1`, `−1`
dispatched on the term index, sentences `incon ⋏ cross` (via `MachineSentenceCodes.and`)
and `cross`, both reindexed to the day.
Source: none: infrastructure (built by hand to keep the import narrow: FAF's
`PolySequence.add` lives under `Construction/Quotation`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
noncomputable def lesionAffine_polySequence (cross incon : ℕ → Sentence)
    (hc : MachineSentenceCodes cross) (hi : MachineSentenceCodes incon) :
    AffineCombination.PolySequence (lesionAffine cross incon) where
  termCount := fun _ => 2
  coefficient := fun z => if z.unpair.2 = 0 then .const 1 else .const (-1)
  sentence := fun z =>
    if z.unpair.2 = 0 then incon z.unpair.1 ⋏ cross z.unpair.1 else cross z.unpair.1
  termCount_poly := UnaryRuler.const 2
  const_poly := MachineSpliceStream.serialize_const 0
  coefficient_poly :=
    ((MachineSpliceStream.serialize_const 1).ifZero (MachineSpliceStream.serialize_const (-1))
      UnaryRuler.unpairSnd).of_eq (fun z => by
        by_cases h : z.unpair.2 = 0 <;> simp [h])
  sentence_poly :=
    (((hi.and hc).comp UnaryRuler.unpairFst).ifZero (hc.comp UnaryRuler.unpairFst)
      UnaryRuler.unpairSnd).of_eq (fun z => by
        by_cases h : z.unpair.2 = 0 <;> simp [h])
  terms_eq := by
    intro n
    have h2 : List.range 2 = [0, 1] := rfl
    simp [lesionAffine, h2, Nat.unpair_pair]
  const_rank := by intro n; simp [lesionAffine]
  coefficient_rank := by intro n j hj; split <;> simp
  const_closed := by intro n ρ V; simp [lesionAffine]
  coefficient_closed := by intro z ρ V; split <;> simp

/-- **The coherence step (target 10; OPEN in round 0, proved in repair round 1).** If the
lesion sentence holds in every completed-theory world, the price of the conjunction
`incon n ⋏ cross n` tracks the price of `cross n`: `P n (incon n ⋏ cross n) − P n (cross n) → 0`.
Proof: in every completed-theory world `v`, `v ⊨ cross n → incon n` makes
`1[incon ⋏ cross] = 1[cross]`, so the value of `lesionAffine n` is `0` there; FAF's
`affine_provind_theory_eq` (the affine provability-induction lemma at `b := 0`) gives the
day-`n` price `→ 0`; the family is polynomial (`lesionAffine_polySequence`), its prices are
bounded by `1` and its magnitude by `2`. No use of `li_lesion_alpha` is needed — the value
argument uses the lesion directly, not through the price of `cross 🡒 incon`.
Source: [[dp-sl-2-inventory]] 034; [[dp-troll-bridge-mandate]] target 10; repair round 1 (fidelity N6)
Kind: C
Fidelity: exact (of the step)
Hyps: (c) `hthm` is the semantic rendering of "T ⊢ cross n → □⊥" -/
theorem li_lesion_conj (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (cross incon : ℕ → Sentence)
    (hc : MachineSentenceCodes cross) (hi : MachineSentenceCodes incon)
    (hthm : ∀ n, ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (cross n 🡒 incon n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (incon n ⋏ cross n) - P n (cross n)) ≈ₙ fun _ => 0 := by
  have hP : ∀ n χ, 0 ≤ P n χ ∧ P n χ ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  have hpoly := lesionAffine_polySequence cross incon hc hi
  have hbounded : BoundedAffinePrices (lesionAffine cross incon) P := by
    refine ⟨1, zero_le_one, fun n m => ?_⟩
    rw [lesionAffine_price, abs_le]
    constructor <;>
      linarith [(hP m (incon n ⋏ cross n)).1, (hP m (incon n ⋏ cross n)).2,
        (hP m (cross n)).1, (hP m (cross n)).2]
  have hmag : ∃ C : ℝ, ∀ n, (lesionAffine cross incon n).magnitude P ≤ C :=
    ⟨2, fun n => by rw [lesionAffine_magnitude]⟩
  have heq := hpoly.affine_provind_theory_eq P DP hbounded hmag hworld 0 (fun n v hv => by
    rw [lesionAffine_value]
    have himp : v.Holds (cross n) → v.Holds (incon n) := (holds_imp v _ _).mp (hthm n v hv)
    by_cases hcr : v.Holds (cross n)
    · have hboth : v.Holds (incon n ⋏ cross n) := (PCWorld.holds_and v _ _).mpr ⟨himp hcr, hcr⟩
      simp [PCWorld.payout, hboth, hcr]
    · have hnot : ¬ v.Holds (incon n ⋏ cross n) := fun h => hcr ((PCWorld.holds_and v _ _).mp h).2
      simp [PCWorld.payout, hnot, hcr])
  have hprice : ∀ n, (lesionAffine cross incon n).price P n =
      P n (incon n ⋏ cross n) - P n (cross n) := fun n => lesionAffine_price cross incon P n n
  unfold AsympEq at heq ⊢
  simpa only [hprice] using heq

/-- **The conditional form, on the `ε`-subsequence.** If the coherence step
`P n (incon n ⋏ cross n) − P n (cross n) → 0` holds (`li_lesion_conj` supplies it for an
inductor), then for every `ε > 0` and `δ > 0`, eventually: whenever `P n (cross n) ≥ ε`, the
capped conditional quote `P_n(incon n | cross n)` is at least `1 − δ`. The restriction to
`P n (cross n) ≥ ε` is essential: `conditionalQuote` is `1` by fiat when the denominator is
`0`, so the unrestricted statement would be vacuously satisfiable. One division bound; holds
for any history `P` (no inductor, no deductive process is used).
Source: [[dp-sl-2-inventory]] 034; `sl-workflow/notes/repair/P11.md` P11-3′ (the `P = 0` clause); [[dp-troll-bridge-mandate]] target 10
Kind: P
Fidelity: variant: the doc's `P(□⊥ | Cross) = 1` becomes an eventual `≥ 1 − δ` on the days with `P(Cross) ≥ ε`
Hyps: (a) `hconj` is the coherence step, discharged by `li_lesion_conj` in `li_lesion_conditional_of_theory` -/
theorem li_lesion_conditional (P : History)
    (cross incon : ℕ → Sentence)
    (hconj : (fun n => P n (incon n ⋏ cross n) - P n (cross n)) ≈ₙ fun _ => 0)
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ε ≤ P n (cross n) →
      1 - δ ≤ conditionalQuote (P n) (incon n) (cross n) := by
  have hεδ : 0 < ε * δ := mul_pos hε hδ
  have ht : Tendsto (fun n => (P n (incon n ⋏ cross n) - P n (cross n)) - 0) atTop (𝓝 0) :=
    hconj
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp ht) (ε * δ) hεδ
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn hPc => ?_⟩
  have hd := hN n hn
  rw [Real.dist_eq, sub_zero, sub_zero, abs_lt] at hd
  have hPc_pos : 0 < P n (cross n) := lt_of_lt_of_le hε hPc
  by_cases hlt : P n (incon n ⋏ cross n) < P n (cross n)
  · rw [conditionalQuote_eq_div hlt, le_div_iff₀ hPc_pos]
    have hmul : ε * δ ≤ P n (cross n) * δ := mul_le_mul_of_nonneg_right hPc hδ.le
    nlinarith [hd.1, hmul]
  · rw [conditionalQuote_eq_one (not_lt.mp hlt)]
    linarith

/-- **The target-10 composite: the LI-level Löbian lesion, (α)-hypothesis to conditional.**
If the lesion sentence `cross n 🡒 incon n` holds in every completed-theory world (the
semantic "T ⊢ Cross_n → □⊥"), then for every `ε, δ > 0`, eventually on every day with
`P n (cross n) ≥ ε` the inductor's capped conditional quote `P_n(incon n | cross n)` is at
least `1 − δ`. This is Lemma 8's credence conclusion `P(□⊥ | Cross) = 1` for an inductor,
in the only form it takes there: asymptotic, and on the non-dogmatic days. No hypothesis is
left open (round 0 left the coherence step OPEN).
Source: [[dp-sl-2-inventory]] 034; [[two-lesions-doc-2026-09-18]] §7 Lemma 8 (the credence step); [[dp-troll-bridge-mandate]] target 10; repair round 1
Kind: C
Fidelity: variant: asymptotic and `ε`-restricted where the doc's is exact
Hyps: (c) `hthm` is the semantic rendering of "T ⊢ cross n → □⊥" -/
theorem li_lesion_conditional_of_theory (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (cross incon : ℕ → Sentence)
    (hc : MachineSentenceCodes cross) (hi : MachineSentenceCodes incon)
    (hthm : ∀ n, ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (cross n 🡒 incon n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ε ≤ P n (cross n) →
      1 - δ ≤ conditionalQuote (P n) (incon n) (cross n) :=
  li_lesion_conditional P cross incon (li_lesion_conj P DP cross incon hc hi hthm hworld)
    ε hε δ hδ

/-! ## Target 10: the OPEN statement, and what it is -/

/-- **The day-`n` reduction of the responsive-agent conjecture.** Under `hβ` (the agent's
rule reflected in every completed-theory world through the market's capped conditional
quote — the quote is one metatheoretic real, so `cross n` is decided the same way in every
such world) and `hcon` (some completed-theory world falsifies `incon n`), the day-`n` lesion
"`cross n 🡒 incon n` holds in every completed-theory world" is *equivalent* to
`½ ≤ conditionalQuote (P n) (incon n) (cross n)`, i.e. "the rule says stay on day `n`". So
the OPEN conjecture below is exactly "the LI-based responsive agent eventually provably
stays" — the LI-level form of finding F3 (for a reflected rule, the lesion collapses to
staying). Recorded so the OPEN statement can be read for what it is.
Source: [[dp-sl-2-inventory]] 034; repair round 1 (fidelity N5, adversarial N7)
Kind: L
Fidelity: n/a (a reduction of the OPEN statement's conclusion under its own hypotheses)
Hyps: (c) `hβ`, `hcon` as in `li_responsive_lesion_open` -/
theorem responsive_lesion_day_iff (P : History) (DP : DeductiveProcess)
    (cross incon : ℕ → Sentence) (n : ℕ)
    (hβ : ∀ v : PCWorld, v.ConsistentWithTheory DP →
      (v.Holds (cross n) ↔ 0 < 10 - 20 * conditionalQuote (P n) (incon n) (cross n)))
    (hcon : ∃ v : PCWorld, v.ConsistentWithTheory DP ∧ ¬ v.Holds (incon n)) :
    (∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (cross n 🡒 incon n)) ↔
      (1 / 2 : ℝ) ≤ conditionalQuote (P n) (incon n) (cross n) := by
  constructor
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨v, hv, hni⟩ := hcon
    have hc : v.Holds (cross n) := (hβ v hv).mpr (by linarith)
    exact hni ((holds_imp v _ _).mp (h v hv) hc)
  · intro hq v hv
    rw [holds_imp]
    intro hc
    have := (hβ v hv).mp hc
    linarith

/-- **OPEN: the LI-based responsive agent is afflicted (or not).** The agent's crossing
sentence `cross n` is defined, inside the theory, by its own conditional-quote expected
utility: `cross n` holds in a consistent world iff `10 − 20 · P_n(incon n | cross n) > 0`
(this is (β) with the market's quote in place of the credence; the shape is
`ParadoxResistanceQuote.diagonal_reflected` with the agent's rule in place of the diagonal
comparison). `incon n` is never refuted by the deductive process (T does not prove its own
consistency), but is refuted in the actual world (`hcon`: some completed-theory world makes
`incon n` false). **Question:** does the lesion `T ⊢ cross n → □⊥` — rendered as
"`cross n 🡒 incon n` holds in every completed-theory world" — hold for all large `n`?
**What the question is** (`responsive_lesion_day_iff`): under `hβ` and `hcon`, the
conclusion is equivalent to `∀ᶠ n, ½ ≤ conditionalQuote (P n) (incon n) (cross n)` — "the
agent eventually stays", the LI form of F3; and the junk value `conditionalQuote = 1` at
`P n (cross n) = 0` sits on the *satisfying* side, so a market that drives `P n (cross n)` to
`0` verifies the statement for the junk reason (F14, one level up). **Satisfiability of the
hypothesis package** (`hβ`, `hcon`, `hworld`, the codes, `[IsLogicalInductor P DP]`) is not
established: `hβ` requires the completed theory to decide `cross n` every day in the
direction of the actual day-`n` quote, a diagonal of the `diagonal_reflected` kind; no
witness was sought. The doc's Lemma 8 uses (α) *inside* T at a fixed stage, which an
inductor supplies only in the limit (`li_lesion_alpha`), and P11-3′'s obstruction says the
lemma "`P(cross) = 0` is T-provable when true" is unavailable for a limit-computable `P`.
Which FAF property would replace PA-representability is the research question; the
(α)-bridge and the coherence step (`li_lesion_conj`) are the provable part. Stated as a
conjecture; failure to prove is not evidence either way. No Lean attempt on the eventual
statement itself was made in round 0 or in repair round 1.
Source: [[dp-sl-2-inventory]] 034 (UNREVIEWED in its source ledger); `sl-workflow/notes/repair/P11.md` P11-3′, Open 9; [[dp-troll-bridge-mandate]] target 10
Kind: OPEN
Fidelity: variant: "T ⊢" rendered semantically; (β) rendered through `conditionalQuote`; equivalent to eventual staying
Hyps: (c) `hβ` is the agent's rule reflected in the theory; (c) `hcon` is Σ₁-soundness-as-a-world; satisfiability of the package unknown -/
theorem li_responsive_lesion_open (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (cross incon : ℕ → Sentence)
    (hc : MachineSentenceCodes cross) (hi : MachineSentenceCodes incon)
    (hβ : ∀ n, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      (v.Holds (cross n) ↔ 0 < 10 - 20 * conditionalQuote (P n) (incon n) (cross n)))
    (hcon : ∀ n, ∃ v : PCWorld, v.ConsistentWithTheory DP ∧ ¬ v.Holds (incon n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (cross n 🡒 incon n) := by
  sorry

/-! ## Target 11: Soto's flower obstruction, LI level -/

/-- **OPEN: the flower obstruction.** For a machine-codeable sentence sequence `S` with
`S n ↔ (P n (S n) ≥ p → ψ n)` reflected in every completed-theory world, the price of `S n`
is eventually at least `p − ε` for every `ε > 0` (`liminf P n (S n) ≥ p`). Mechanism (the
inventory's sketch): when `P n (S n) < p` the antecedent fails and `S n` holds in every
consistent world, so a trader buying `S n` whenever its price is below `p − δ` profits `δ` per
unit and would exploit `P`. FAF's `lic_paradox_resistance` is the template (its
`diagonal_reflected` is the case `ψ n := ⊥`, where the sentence says its own price is below
`p`), and it takes its two affine certificates as *fields* of a `ParadoxResistanceQuote`
package (built for the diagonal sentence under `Construction/Quotation`). **Repair round 1:**
`flower_liminf_of_portfolio` (`FlowerLI.lean`) proves this statement *conditional on the
quotation portfolio* — FAF's `AffineQuotePortfolio` for the gated product
`ctsInd (width n) p (P n (S n)) · (1 − P n (S n))` with its per-world value law — deriving
the certificate's completed-theory coherence from `hrefl` (below `p` the antecedent fails, so
`S n` holds in every completed-theory world); `ψ` drops out. What remains open here is the
portfolio itself: the EF-gated family with machine-metered emission, which FAF builds for
the paradox sentence from a `MarketComputation` and an arithmetic fixed point
(`paradoxResistanceQuoteOfDiagonal`, heavy imports); not attempted. The source attributes
the effect to self-trust; the mechanism is the buying trader (findings).
Source: Soto 2023 "Argmaxing our strategy" p. 3 (Picking flowers); [[bli-soto-b-inventory]] 004; [[dp-troll-bridge-mandate]] target 11
Kind: OPEN
Fidelity: exact (of the inventory's precise reading)
Hyps: (c) `hrefl` is the self-referential sentence's reflection in the theory -/
theorem flower_liminf_open (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (S ψ : ℕ → Sentence) (hS : MachineSentenceCodes S)
    (hrefl : ∀ n, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      (v.Holds (S n) ↔ ((p : ℝ) ≤ P n (S n) → v.Holds (ψ n))))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, (p : ℝ) - ε ≤ P n (S n) := by
  sorry

end Cleanroom.Decision.DpTrollBridge
