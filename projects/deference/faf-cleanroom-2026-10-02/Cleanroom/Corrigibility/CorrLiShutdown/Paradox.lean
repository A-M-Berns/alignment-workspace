import Cleanroom.Corrigibility.CorrLiShutdown.Legitimacy
import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Framework.Machine.SentenceMachine

/-!
# `corr-li-shutdown` — Paradox (T2(c)): the exact self-trust inequality fails on the paradoxical
family — PROVED (repair round 2)

Round 0 stated T2(c) OPEN (`exact_selfTrust_refuted_open`, `Legitimacy.lean`): on FAF's
constructed diagonal family `χ_n ↔ (P_n(χ_n) < 1/2)` over the paper inductor, with the event
"`P_n(χ_n) ≥ 1/2`" read as `∼χ_n` through the diagonal, the hard-indicator self-trust
inequality at `p = 1/2`, `P_n(χ_n ⋏ ∼χ_n) ≳ₙ (1/2)·P_n(∼χ_n)`, is false. The two missing
inputs (audit r1 fidelity N7, audit r2 fidelity N3) are built here:

* **the e.c. certificates** of `n ↦ ∼χ_n` and `n ↦ χ_n ⋏ ∼χ_n`, from the quote code's
  `BooleanQuoteCode.sentence_poly` by `PolyFueled` pairing against Foundation's `Formula.toNat`
  (`∼φ = φ 🡒 ⊥` is tag `2`, `⋏` is tag `3`);
* **the negation-price complement** `P_n(χ_n) + P_n(∼χ_n) ≈ₙ 1`, as FAF's affine provability
  induction (`PolySequence.affine_provind_theory_eq`) on the **two-share** affine family
  `χ_n + ∼χ_n`, whose value is `1` in every world; its `PolySequence` certificate interleaves
  the two sentence families by the residue of the term index
  (`MachineSentenceCodes.modDispatch`).

Then `thm:provind` (negative polarity) on the propositionally refutable conjunction gives
`P_n(χ_n ⋏ ∼χ_n) → 0`, FAF's `thm:lp` gives `P_n(χ_n) → 1/2`, hence `P_n(∼χ_n) → 1/2`, and the
inequality fails at `ε = 1/8`: `(1/2)·P_n(∼χ_n) → 1/4 > 0`.

The event is FAF's own literal (audit r3 adversarial N2): `χ_n` is FAF's quotation literal for
the decision "`P_n(χ_n) < 1/2`" (`BooleanQuoteCode.sentence`), and
`ParadoxResistanceQuote.diagonal_reflected` makes `∼χ_n` the sentence for "`P_n(χ_n) ≥ 1/2`" in
every theory-consistent world. What is a variant of the sources' claim is the **day** (FAF's
family is at the diagonal day `n`, the sources' at `f(n)` — that identification is
ATTRIBUTION-UNVETTED) and the hard event in place of `st`'s ramp; the theorem is about FAF's
family. Its content is `thm:lp`: `P_n(χ_n ⋏ ∼χ_n) → 0` holds for *every* e.c. family
(`thm:provind` on a refutable conjunction), so the inequality fails exactly when `P_n(∼χ_n)` does
not vanish — which on the paradoxical family it does not. Surviving neighbour: the ramp-weighted
`st` (`Map.lean`, `selfTrust_is_anticipation`).
-/

namespace Cleanroom.Corrigibility.CorrLiShutdown

open LogicalInduction LogicalInduction.AffineCombination Filter Topology
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

/-! ## A. Two-share affine families -/

/-- The two-share affine combination `φ n + ψ n`.
Source: none: infrastructure (FAF's `sentenceAffine`, two terms)
Kind: D
Fidelity: n/a -/
def twoShareAffine (φ ψ : ℕ → Sentence) (n : ℕ) : AffineCombination where
  const := .const 0
  terms := [(.const 1, φ n), (.const 1, ψ n)]

/-- Two sentence families selected by a term index: `0 ↦ φ`, `j + 1 ↦ ψ`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def twoFam (φ ψ : ℕ → Sentence) : ℕ → ℕ → Sentence
  | 0 => φ
  | _ + 1 => ψ

/-- Both selected families are machine-coded.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoFam_codes {φ ψ : ℕ → Sentence} (hφ : MachineSentenceCodes φ)
    (hψ : MachineSentenceCodes ψ) : ∀ j < 2, MachineSentenceCodes (twoFam φ ψ j) := by
  intro j hj
  interval_cases j
  · exact hφ
  · exact hψ

/-- **The two-share family is a `PolySequence`** when both sentence families are e.c.: the
term-index pairing `⟨n, j⟩` reads `φ n` at `j = 0` and `ψ n` at `j = 1`, assembled by FAF's
`MachineSentenceCodes.modDispatch`.
Source: none: infrastructure (FAF `sentenceAffine_polySequence`, two terms; `MachineSentenceCodes.modDispatch`)
Kind: L
Fidelity: n/a -/
noncomputable def twoShareAffine_polySequence (φ ψ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (hψ : MachineSentenceCodes ψ) : PolySequence (twoShareAffine φ ψ) :=
  {
    termCount := fun _ => 2
    coefficient := fun _ => .const 1
    sentence := fun z => twoFam φ ψ (z.unpair.2 % 2) z.unpair.1
    termCount_poly := UnaryRuler.const 2
    const_poly := MachineSpliceStream.serialize_const 0
    coefficient_poly := MachineSpliceStream.serialize_const 1
    sentence_poly := MachineSentenceCodes.modDispatch (by norm_num) (twoFam_codes hφ hψ)
    terms_eq := by intro n; simp [twoShareAffine, List.range_succ, twoFam]
    const_rank := by intro n; simp [twoShareAffine]
    coefficient_rank := by intro n j hj; simp [EF.rank]
    const_closed := by intro n ρ V; simp [twoShareAffine]
    coefficient_closed := by intro z ρ V; simp [EF.denoteWith]
  }

/-- The price of the two-share family is the sum of the two prices.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma twoShareAffine_price (φ ψ : ℕ → Sentence) (P : History) (n m : ℕ) :
    (twoShareAffine φ ψ n).price P m = P m (φ n) + P m (ψ n) := by
  simp [twoShareAffine, AffineCombination.price, AffineCombination.value]

/-- The value of the two-share family at a valuation is the sum of the two values.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoShareAffine_value (φ ψ : ℕ → Sentence) (P : History) (n : ℕ) (w : Valuation) :
    (twoShareAffine φ ψ n).value P w = w (φ n) + w (ψ n) := by
  simp [twoShareAffine, AffineCombination.value]

/-- The magnitude of the two-share family is `2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoShareAffine_magnitude (φ ψ : ℕ → Sentence) (P : History) (n : ℕ) :
    (twoShareAffine φ ψ n).magnitude P = 2 := by
  simp [twoShareAffine, AffineCombination.magnitude]
  norm_num

/-- **The negation complement along an e.c. family** (affine coherence): for e.c. `χ` with
e.c. negations, `P_n(χ_n) + P_n(∼χ_n) ≈ₙ 1` — FAF's affine provability induction on the
two-share family `χ_n + ∼χ_n`, whose value is `1` in every world.
Source: LI paper `thm:affprovind` (FAF `PolySequence.affine_provind_theory_eq`); audit r1 fidelity N7 (the "negation-price lemma")
Kind: C
Fidelity: exact
Hyps: (a) (`hneg`: the negated family's own certificate, derived for the paradoxical family below) -/
theorem price_add_price_neg_asymp (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (χ : ℕ → Sentence) (hχ : MachineSentenceCodes χ)
    (hneg : MachineSentenceCodes (fun n => ∼ χ n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (χ n) + P n (∼ χ n)) ≈ₙ fun _ => 1 := by
  have hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1 :=
    fun n ψ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n ψ
  have h := PolySequence.affine_provind_theory_eq
    (twoShareAffine_polySequence χ (fun n => ∼ χ n) hχ hneg) P DP
    ⟨2, by norm_num, fun n m => by
      rw [twoShareAffine_price, abs_le]
      constructor <;> linarith [(hP m (χ n)).1, (hP m (χ n)).2, (hP m (∼ χ n)).1,
        (hP m (∼ χ n)).2]⟩
    ⟨2, fun n => by rw [twoShareAffine_magnitude]⟩ hworld 1
    (fun n v _ => by
      rw [twoShareAffine_value]
      by_cases hh : v.Holds (χ n) <;> simp [PCWorld.payout, hh])
  simpa [twoShareAffine_price] using h

/-! ## B. The paradoxical family and its certificates -/

section ParadoxCodes

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]

/-- FAF's constructed diagonal family at threshold `1/2` over the paper inductor:
`χ_n ↔ (P_n(χ_n) < 1/2)`.
Source: FAF `paperDiagonalQuoteCode` (`thm:lp`)
Kind: D
Fidelity: n/a -/
noncomputable abbrev paradoxSentence (n : ℕ) : Sentence :=
  (paperDiagonalQuoteCode T (1 / 2)).toBooleanQuoteCode.sentence n

/-- The family is e.c. (the quote code's own emitter).
Source: FAF `BooleanQuoteCode.sentence_poly`
Kind: L
Fidelity: n/a -/
lemma paradox_polyCodes : PolySentenceCodes (paradoxSentence T) :=
  (paperDiagonalQuoteCode T (1 / 2)).toBooleanQuoteCode.sentence_poly

/-- `MachineSentenceCodes` for the family.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma paradox_codes : MachineSentenceCodes (paradoxSentence T) :=
  RpnSentenceCodes.toMachine (RpnSentenceCodes.ofPolySentenceCodes (paradox_polyCodes T))

/-- The negated family `n ↦ ∼χ_n` is e.c. (`∼φ = φ 🡒 ⊥` encodes as `⟨2, ⟨⌜φ⌝, 1⟩⟩ + 1`).
Source: none: infrastructure (the `neg_pressAtom_polySentenceCodes` pattern)
Kind: L
Fidelity: n/a -/
lemma paradox_neg_polyCodes : PolySentenceCodes (fun n => ∼ paradoxSentence T n) := by
  obtain ⟨c, hc⟩ := paradox_polyCodes T
  exact ⟨_, (((PolyFueled.const 2).pair (hc.pair (PolyFueled.const 1))).succ_comp).of_eq
    fun n => by
      show Nat.pair 2 (Nat.pair (Encodable.encode (paradoxSentence T n)) 1) + 1 = _
      rfl⟩

/-- `MachineSentenceCodes` for the negated family.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma paradox_neg_codes : MachineSentenceCodes (fun n => ∼ paradoxSentence T n) :=
  RpnSentenceCodes.toMachine (RpnSentenceCodes.ofPolySentenceCodes (paradox_neg_polyCodes T))

/-- The conjunction family `n ↦ χ_n ⋏ ∼χ_n` is e.c. (`⋏` encodes as `⟨3, ⟨⌜φ⌝, ⌜ψ⌝⟩⟩ + 1`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma paradox_conj_polyCodes :
    PolySentenceCodes (fun n => paradoxSentence T n ⋏ ∼ paradoxSentence T n) := by
  obtain ⟨c, hc⟩ := paradox_polyCodes T
  exact ⟨_, (((PolyFueled.const 3).pair (hc.pair
      (((PolyFueled.const 2).pair (hc.pair (PolyFueled.const 1))).succ_comp))).succ_comp).of_eq
    fun n => by
      show Nat.pair 3 (Nat.pair (Encodable.encode (paradoxSentence T n))
        (Nat.pair 2 (Nat.pair (Encodable.encode (paradoxSentence T n)) 1) + 1)) + 1 = _
      rfl⟩

/-- `MachineSentenceCodes` for the conjunction family.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma paradox_conj_codes :
    MachineSentenceCodes (fun n => paradoxSentence T n ⋏ ∼ paradoxSentence T n) :=
  RpnSentenceCodes.toMachine (RpnSentenceCodes.ofPolySentenceCodes (paradox_conj_polyCodes T))

end ParadoxCodes

/-! ## C. The three limits and the refutation -/

section Paradox

variable (T : ArithmeticTheory) [T.Δ₁] [Entailment.Consistent T] [𝗜𝚺₁ ⪯ T]

/-- `P_n(χ_n ⋏ ∼χ_n) → 0`: `thm:provind`, negative polarity, on the propositionally refutable
conjunction (false in every world).
Source: FAF `lic_provind_false`; LI paper `main.tex:2110` ("with discrete conjunctions … false")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem paradox_conj_price_tendsto_zero :
    (fun n => liaHistory (paperDP T) n (paradoxSentence T n ⋏ ∼ paradoxSentence T n)) ≈ₙ
      fun _ => 0 := by
  haveI := paperLIA T
  exact lic_provind_false (liaHistory (paperDP T)) (paperDP T) _ (paradox_conj_codes T)
    (fun n v _ => by simp only [PCWorld.holds_neg, PCWorld.holds_and]; tauto)
    (paperDP_hworld T)

/-- `P_n(∼χ_n) → 1/2`: the complement of `thm:lp`'s `P_n(χ_n) → 1/2` through
`price_add_price_neg_asymp`.
Source: FAF `lic_paradox_resistance_ofDiagonal_unconditional` (`thm:lp`); affine coherence
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem paradox_neg_price_tendsto_half :
    (fun n => liaHistory (paperDP T) n (∼ paradoxSentence T n)) ≈ₙ fun _ => (1 / 2 : ℝ) := by
  haveI := paperLIA T
  have hsum := price_add_price_neg_asymp (liaHistory (paperDP T)) (paperDP T)
    (paradoxSentence T) (paradox_codes T) (paradox_neg_codes T) (paperDP_hworld T)
  have hχ := lic_paradox_resistance_ofDiagonal_unconditional T (1 / 2) (by norm_num) (by norm_num)
  unfold AsympEq at hsum hχ ⊢
  have h := hsum.sub hχ
  rw [_root_.sub_zero] at h
  refine h.congr' (Eventually.of_forall fun n => ?_)
  push_cast
  ring

/-- **T2(c), PROVED: the exact (hard-indicator) self-trust inequality fails on FAF's paradoxical
family.** Let `χ_n` be FAF's constructed diagonal sentence `χ_n ↔ (P_n(χ_n) < 1/2)` over the paper
inductor: `χ_n` is FAF's quotation literal for the decision "`P_n(χ_n) < 1/2`"
(`BooleanQuoteCode.sentence`), so `∼χ_n` is FAF's own sentence for the event "`P_n(χ_n) ≥ 1/2`"
(`ParadoxResistanceQuote.diagonal_reflected`, in every theory-consistent world) — the event needs
no reading. Then the hard-indicator self-trust inequality at `p = 1/2`,
`P_n(χ_n ⋏ ∼χ_n) ≳ₙ (1/2)·P_n(∼χ_n)`, **fails**: the left side tends to `0`
(`paradox_conj_price_tendsto_zero`, `thm:provind` on the refutable conjunction — true for *every*
e.c. family) while the right side tends to `1/4` (`paradox_neg_price_tendsto_half`: `thm:lp`
plus the complement), so the inequality fails exactly because the event keeps probability `1/2`
on the paradoxical family — the content is `thm:lp`; at `ε = 1/8` the inequality is eventually
violated. What is a variant of the sources' claim: the **day** (FAF's family is at the diagonal
day `n`, the sources' at `f(n)` — that identification is ATTRIBUTION-UNVETTED) and the hard
event in place of `st`'s ramp. The paper's own remark (`main.tex:2110`): "with discrete
conjunctions, the result would be undesirable (not to mention false)". Statement verbatim the
round-0 OPEN `exact_selfTrust_refuted_open`. Kind C (audit r3 fidelity N2, adversarial N2): a
composition of `thm:provind`, `thm:lp` and `thm:affprovind` through the certificates and the
complement built in this file. Surviving neighbour: the ramp-weighted `st`
(`lic_self_trust_closed`; T8).
Source: [[corr-wf13-inventory]] 067; [[corr-wf14-inventory]] 090 (`li-final.md` Statement 6, bifurcation caveat, l. 84); [[corr-wf14b-inventory]] 058; LI paper `main.tex:2110–2126`
Kind: C
Fidelity: variant: diagonal-day family (FAF's; the sources' is at `f(n)` — ATTRIBUTION-UNVETTED); hard event in place of `st`'s ramp, as FAF's own literal `∼χ_n`
Hyps: (a) -/
theorem exact_selfTrust_refuted :
    ¬ ((fun n => liaHistory (paperDP T) n
          ((paperDiagonalQuoteCode T (1 / 2)).toBooleanQuoteCode.sentence n ⋏
            ∼ (paperDiagonalQuoteCode T (1 / 2)).toBooleanQuoteCode.sentence n)) ≳ₙ
        fun n => (1 / 2 : ℝ) * liaHistory (paperDP T) n
          (∼ (paperDiagonalQuoteCode T (1 / 2)).toBooleanQuoteCode.sentence n)) := by
  intro hge
  have hconj := paradox_conj_price_tendsto_zero T
  have hneg := paradox_neg_price_tendsto_half T
  have h1 := hge (1 / 8) (by norm_num)
  have h2 := (Metric.tendsto_nhds.mp hconj) (1 / 16) (by norm_num)
  have h3 := (Metric.tendsto_nhds.mp hneg) (1 / 16) (by norm_num)
  obtain ⟨n, hn1, hn2, hn3⟩ := (h1.and (h2.and h3)).exists
  simp only [Real.dist_eq, _root_.sub_zero, abs_lt] at hn2 hn3
  linarith [hn2.2, hn3.1]

end Paradox

end Cleanroom.Corrigibility.CorrLiShutdown
