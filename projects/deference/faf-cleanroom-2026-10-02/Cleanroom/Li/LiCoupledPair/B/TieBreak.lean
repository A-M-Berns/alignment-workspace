import LogicalInduction.Properties.ExpectationAffine
import LogicalInduction.Properties.NonDogmatism
import LogicalInduction.Properties.AffinePersistence
import LogicalInduction.Properties.Relationships

/-!
# `li-coupled-pair` · B · TieBreak: the ψ-tie-break counterexample (T3.3)

[[ledger-decided-tie-breaks]] (lean-deference-074, lean-deference-2-019): a tie-break rule that
is definable but not ledger-decided breaks F1 by correlation. The page's counterexample: an
undecidable `ψ`, the menu `O¹ = 𝟙_ψ`, `O² = 𝟙_{¬ψ}`; the *clairvoyant* rule ("select `O¹` iff `ψ`")
gives a followed strategy `Ŝ_c = 𝟙_ψ·𝟙_ψ + 𝟙_{¬ψ}·𝟙_{¬ψ} = 1` in every world, so
`E*(Ŝ_c) = 1 > ½ = max`; the *adversarial* rule ("select `O¹` iff `¬ψ`") gives `Ŝ_a ≡ 0`, so
`E*(Ŝ_a) = 0 < ½` and Value fails outright. The page grades itself "PROVED (prose) … would be a
very easy finite-exact Lean check".

**Finite-exact form** (`psiTieBreak_finite`). Over FAF's `[0,1]`-LUV presentation the followed
strategies are the indicator LUVs (`LUV.indicatorOf`) of the sentences
`(ψ ⋏ ψ) ⋎ (∼ψ ⋏ ∼ψ)` and `(∼ψ ⋏ ψ) ⋎ (ψ ⋏ ∼ψ)` — the propositional renderings of the products —
and *every* world (`PCWorld`, no consistency with any process needed) values `Ŝ_c` at `1`, `Ŝ_a`
at `0`, and the menu at `𝟙_ψ`, `1 − 𝟙_ψ`. No `½` enters the per-world identities: the expert
never does.

**Logical-inductor form** (`psiTieBreak_LI`, the mandate's stretch), Fidelity `variant` (repair
round 1; it was `stronger`): for an inductor `P` over `DP` with `ψ` undecided on both sides, the
day-`n` expectations of `Ŝ_c` converge to `1` and of `Ŝ_a` to `0` (FAF's `thm:ei` on
`thm:provind`'s `⊤`- and `⊥`-equivalents), the menu expectations converge to `ℙ∞(ψ)` and
`1 − ℙ∞(ψ)` (`thm:ei`, `thm:lex` for the complement), and `max (ℙ∞ ψ) (1 − ℙ∞ ψ) < 1 < …` —
strictly — because `0 < ℙ∞(ψ) < 1` by `thm:nd` (`lic_nonDogmatism`, both sides). So the overshoot
`1 > max` and the undershoot `0 < min` hold for every inductor and every undecided `ψ`. **What
this drops is the page's tie** (audit r1, fidelity B1): the page's `P(ψ) = ½` is what makes the
menu tie (argmax set `{1, 2}`) and its two rules *tie-break rules of the argmax strategy* — the
page's subject. With `ℙ∞ψ ≠ ½` the argmax set is a singleton and "select `O¹` iff `ψ`" is a
world-dependent selector, not a tie-break; the LI form proves the F1-violation inequality for
such a selector. The tie-break reading needs `ℙ∞ψ = ½`, which no FAF theorem supplies. So the
`½` is not decoration (findings F-B5 rewritten accordingly); the mandate's T3.3 instruction
("decoration; Fidelity `stronger`") is overridden by STANDARDS §3 (report, conflicts flagged).

**Refutation-row discipline** (plan §0.4 rule 3). Nothing here refutes the page: its counterexample
is confirmed (and strengthened). The page's sentence "*Ledger-decided ⟺ computable from the
ledger*" is angle A's T3.1; the reading of "ledger-decided" as "decided in a stage and provably
unique" is the mandate's (ATTRIBUTION-UNVETTED against the page's author, who marks the page
"unvetted by Abram"). Scope: one market (the expert's), one-way.
-/

namespace Cleanroom.Li.LiCoupledPair.B

open LogicalInduction LO.Propositional Filter Topology

/-! ## A. The menu and the two rules -/

/-- The clairvoyant rule's followed strategy, as a sentence: "select `O¹` iff `ψ`" gives
`𝟙_ψ · 𝟙_ψ + 𝟙_{¬ψ} · 𝟙_{¬ψ}`, i.e. `(ψ ⋏ ψ) ⋎ (∼ψ ⋏ ∼ψ)`.
Source: [[ledger-decided-tie-breaks]] §"What F1 does require" (clairvoyant rule)
Kind: D
Fidelity: exact (the product-sum rendered propositionally)
Hyps: n/a -/
def clairvoyantRule (ψ : Sentence) : Sentence := (ψ ⋏ ψ) ⋎ (∼ψ ⋏ ∼ψ)

/-- The adversarial rule's followed strategy: "select `O¹` iff `¬ψ`" gives
`𝟙_{¬ψ} · 𝟙_ψ + 𝟙_ψ · 𝟙_{¬ψ}`, i.e. `(∼ψ ⋏ ψ) ⋎ (ψ ⋏ ∼ψ)`.
Source: [[ledger-decided-tie-breaks]] §"What F1 does require" (adversarial rule)
Kind: D
Fidelity: exact
Hyps: n/a -/
def adversarialRule (ψ : Sentence) : Sentence := (∼ψ ⋏ ψ) ⋎ (ψ ⋏ ∼ψ)

/-- The menu's first option `O¹ = 𝟙_ψ` (FAF's indicator LUV).
Source: [[ledger-decided-tie-breaks]] (the counterexample's menu)
Kind: D
Fidelity: exact
Hyps: n/a -/
def menuTrue (ψ : Sentence) : LUV := LUV.indicatorOf ψ

/-- The menu's second option `O² = 𝟙_{¬ψ}`.
Source: [[ledger-decided-tie-breaks]]
Kind: D
Fidelity: exact
Hyps: n/a -/
def menuFalse (ψ : Sentence) : LUV := LUV.indicatorOf (∼ψ)

/-- `Ŝ_c`, the clairvoyant rule's followed strategy as a LUV.
Source: [[ledger-decided-tie-breaks]]
Kind: D
Fidelity: exact
Hyps: n/a -/
def clairvoyantStrategy (ψ : Sentence) : LUV := LUV.indicatorOf (clairvoyantRule ψ)

/-- `Ŝ_a`, the adversarial rule's followed strategy as a LUV.
Source: [[ledger-decided-tie-breaks]]
Kind: D
Fidelity: exact
Hyps: n/a -/
def adversarialStrategy (ψ : Sentence) : LUV := LUV.indicatorOf (adversarialRule ψ)

/-- The clairvoyant rule holds in every world (`ψ` or `¬ψ`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_clairvoyantRule (v : PCWorld) (ψ : Sentence) : v.Holds (clairvoyantRule ψ) := by
  unfold clairvoyantRule
  rw [PCWorld.holds_or, PCWorld.holds_and, PCWorld.holds_and, PCWorld.holds_neg]
  tauto

/-- The adversarial rule holds in no world.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma not_holds_adversarialRule (v : PCWorld) (ψ : Sentence) : ¬ v.Holds (adversarialRule ψ) := by
  unfold adversarialRule
  rw [PCWorld.holds_or, PCWorld.holds_and, PCWorld.holds_and, PCWorld.holds_neg]
  tauto

/-! ## B. The finite-exact form -/

/-- **An indicator LUV is valued at the payout of its sentence in every world** — the
threshold-coherence reading of `𝟙_φ ∈ {0, 1}`: thresholds below `0` are `⊤`, thresholds in
`[0,1)` are `φ ⋏ ∼∼φ`, thresholds at or above `1` are `⊥`.
Source: none: infrastructure (FAF `LUV.indicatorOf`, `PCWorld.ValuesAt`)
Kind: P
Fidelity: n/a
Hyps: (a) none -/
theorem indicatorOf_valuesAt (v : PCWorld) (φ : Sentence) :
    v.ValuesAt (LUV.indicatorOf φ) (v.payout φ) := by
  have hbot : ¬ v.Holds (⊥ : Sentence) := by
    simp [PCWorld.Holds, LO.Propositional.Formula.Boolean.val]
  unfold PCWorld.ValuesAt PCWorld.payout
  by_cases h : v.Holds φ
  · rw [if_pos h]
    refine ⟨zero_le_one, le_rfl, fun r => ⟨fun hr => ?_, fun hr => ?_⟩⟩
    · have hr' : r < 1 := by exact_mod_cast hr
      show v.Holds (if r < 0 then (⊤ : Sentence) else if r < 1 then φ ⋏ ∼∼φ else (⊥ : Sentence))
      by_cases h0 : r < 0
      · rw [if_pos h0]; exact PCWorld.holds_top v
      · rw [if_neg h0, if_pos hr', PCWorld.holds_and, PCWorld.holds_neg, PCWorld.holds_neg]
        exact ⟨h, fun hn => hn h⟩
    · have hr' : 1 < r := by exact_mod_cast hr
      show ¬ v.Holds (if r < 0 then (⊤ : Sentence) else if r < 1 then φ ⋏ ∼∼φ else (⊥ : Sentence))
      rw [if_neg (by linarith), if_neg (by linarith)]
      exact hbot
  · rw [if_neg h]
    refine ⟨le_rfl, zero_le_one, fun r => ⟨fun hr => ?_, fun hr => ?_⟩⟩
    · have hr' : r < 0 := by exact_mod_cast hr
      show v.Holds (if r < 0 then (⊤ : Sentence) else if r < 1 then φ ⋏ ∼∼φ else (⊥ : Sentence))
      rw [if_pos hr']; exact PCWorld.holds_top v
    · have hr' : 0 < r := by exact_mod_cast hr
      show ¬ v.Holds (if r < 0 then (⊤ : Sentence) else if r < 1 then φ ⋏ ∼∼φ else (⊥ : Sentence))
      rw [if_neg (by linarith)]
      by_cases h1 : r < 1
      · rw [if_pos h1, PCWorld.holds_and]
        exact fun hc => h hc.1
      · rw [if_neg h1]; exact hbot

/-- The payout of `∼ψ` is `1 − 𝟙_ψ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_neg (v : PCWorld) (ψ : Sentence) : v.payout (∼ψ) = 1 - v.payout ψ := by
  unfold PCWorld.payout
  rw [PCWorld.holds_neg]
  by_cases h : v.Holds ψ <;> simp [h]

/-- **T3.3, finite-exact (the page's counterexample, checked in every world).** In every world
`v`: the clairvoyant strategy is valued at `1`, the adversarial strategy at `0`, the menu at
`𝟙_ψ` and `1 − 𝟙_ψ`. So `E*(Ŝ_c) = 1 > max(E*(O¹), E*(O²))` and `E*(Ŝ_a) = 0 < min(…)` hold for any
coherent expert whose credence in `ψ` is strictly between `0` and `1` — the page's `½` is not
used. Scope: one market.
Source: [[ledger-decided-tie-breaks]] §"What F1 does require — and the correlation counterexample" (lean-deference-074, lean-deference-2-019); mandate T3.3
Kind: N (finite-exact)
Fidelity: stronger: holds in every world with no `P(ψ) = ½` and no process; the products are rendered propositionally
Hyps: (a) none -/
theorem psiTieBreak_finite (v : PCWorld) (ψ : Sentence) :
    v.ValuesAt (clairvoyantStrategy ψ) 1 ∧ v.ValuesAt (adversarialStrategy ψ) 0 ∧
      v.ValuesAt (menuTrue ψ) (v.payout ψ) ∧ v.ValuesAt (menuFalse ψ) (1 - v.payout ψ) := by
  refine ⟨?_, ?_, indicatorOf_valuesAt v ψ, ?_⟩
  · have h := indicatorOf_valuesAt v (clairvoyantRule ψ)
    rwa [PCWorld.payout, if_pos (holds_clairvoyantRule v ψ)] at h
  · have h := indicatorOf_valuesAt v (adversarialRule ψ)
    rwa [PCWorld.payout, if_neg (not_holds_adversarialRule v ψ)] at h
  · rw [← payout_neg]; exact indicatorOf_valuesAt v (∼ψ)

/-! ## C. The logical-inductor form -/

/-- `ℙ∞(ψ) + ℙ∞(∼ψ) = 1` for an inductor (`thm:lex` at the two-member family `{ψ, ∼ψ}`, through
`lic_limitingBelief_tendsto`).
Source: FAF `lic_learning_exclusive_exhaustive`, `lic_limitingBelief_tendsto`
Kind: L
Fidelity: n/a -/
lemma limitingBelief_add_neg (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (ψ : Sentence) :
    limitingBelief P ψ + limitingBelief P (∼ψ) = 1 := by
  let φ : ℕ → ℕ → Sentence := fun j _ => if j = 0 then ψ else ∼ψ
  have hcodes : ∀ j < 2, MachineSentenceCodes (φ j) := fun j _ => MachineSentenceCodes.const _
  have hexact : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ((List.range 2).map (fun j => v.payout (φ j n))).sum = 1 := by
    intro n v _
    simp only [φ, List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.nil_append, List.cons_append, if_true, Nat.one_ne_zero, if_false]
    rw [payout_neg]; ring
  have hlex := lic_learning_exclusive_exhaustive P DP 2 (by norm_num) φ hcodes hworld hexact
  have hone : ConvergesTo (fun n => P n ψ + P n (∼ψ)) 1 := by
    refine (convergesTo_iff_asympEq_const.mpr hlex).congr fun n => ?_
    simp only [φ, List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.nil_append, List.cons_append, if_true, Nat.one_ne_zero, if_false]
    ring
  have hsum : ConvergesTo (fun n => P n ψ + P n (∼ψ)) (limitingBelief P ψ + limitingBelief P (∼ψ)) :=
    (lic_limitingBelief_tendsto P DP hworld ψ).add (lic_limitingBelief_tendsto P DP hworld (∼ψ))
  exact tendsto_nhds_unique hsum hone

/-- `0 < ℙ∞(ψ)` when `ψ` is consistent with every stage (`thm:nd` in the limit).
Source: FAF `lic_nonDogmatism`, `lic_limitingBelief_tendsto`
Kind: L
Fidelity: n/a -/
lemma limitingBelief_pos (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (ψ : Sentence)
    (hpos : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds ψ) :
    0 < limitingBelief P ψ := by
  obtain ⟨ε, hε, hev⟩ := lic_nonDogmatism P DP ψ hpos
  exact lt_of_lt_of_le hε (ge_of_tendsto (lic_limitingBelief_tendsto P DP hworld ψ) hev)

/-- **T3.3, the logical-inductor form (stretch).** For an inductor `P` over `DP` with `ψ`
undecided on both sides: the expectations of the clairvoyant and adversarial strategies converge
to `1` and `0`, the menu expectations converge to `ℙ∞(ψ)` and `1 − ℙ∞(ψ)`, and
`max (ℙ∞ ψ) (1 − ℙ∞ ψ) < 1`, `0 < min (ℙ∞ ψ) (1 − ℙ∞ ψ)`: the overshoot and the undershoot are
strict. `hworld` alone gives the first two conjuncts; `hpos`/`hneg` enter only through
non-dogmatism, for the menu limits and the strict inequalities. The page's tie (`P(ψ) = ½`, which
makes its rules tie-breaks of the argmax strategy) is dropped: see the module docstring. Scope:
one market.
Source: [[ledger-decided-tie-breaks]] (the counterexample, read for a logical inductor); mandate T3.3 (LI form); FAF `thm:ei`, `thm:provind`, `thm:nd`, `thm:lex`
Kind: C
Fidelity: variant: the tie (and the expert's stipulated credence `½`) dropped — the conclusion is the page's F1-violation inequality for a world-dependent selector; the "tie-break" reading needs `ℙ∞ψ = ½`, which no FAF theorem supplies; limits in place of the page's single coherent expert
Hyps: (a) none (`hpos`/`hneg` are the page's "`ψ` undecidable", rendered stagewise) -/
theorem psiTieBreak_LI (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (ψ : Sentence) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hpos : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds ψ)
    (hneg : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds (∼ψ)) :
    ConvergesTo (fun n => (clairvoyantStrategy ψ).expect P n) 1 ∧
      ConvergesTo (fun n => (adversarialStrategy ψ).expect P n) 0 ∧
      ConvergesTo (fun n => (menuTrue ψ).expect P n) (limitingBelief P ψ) ∧
      ConvergesTo (fun n => (menuFalse ψ).expect P n) (1 - limitingBelief P ψ) ∧
      max (limitingBelief P ψ) (1 - limitingBelief P ψ) < 1 ∧
      0 < min (limitingBelief P ψ) (1 - limitingBelief P ψ) := by
  have hadd := limitingBelief_add_neg P DP hworld ψ
  have hposL := limitingBelief_pos P DP hworld ψ hpos
  have hnegL := limitingBelief_pos P DP hworld (∼ψ) hneg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hei := lic_expectation_indicator_unconditional P DP (fun _ => clairvoyantRule ψ)
      (MachineSentenceCodes.const _) hworld
    have hprov := lic_provind_true P DP (fun _ => clairvoyantRule ψ) (MachineSentenceCodes.const _)
      (fun _ v _ => holds_clairvoyantRule v ψ) hworld
    exact convergesTo_iff_asympEq_const.mpr (hei.trans hprov)
  · have hei := lic_expectation_indicator_unconditional P DP (fun _ => adversarialRule ψ)
      (MachineSentenceCodes.const _) hworld
    have hprov := lic_provind_false P DP (fun _ => adversarialRule ψ) (MachineSentenceCodes.const _)
      (fun _ v _ => (PCWorld.holds_neg v _).mpr (not_holds_adversarialRule v ψ)) hworld
    exact convergesTo_iff_asympEq_const.mpr (hei.trans hprov)
  · have hei := lic_expectation_indicator_unconditional P DP (fun _ => ψ)
      (MachineSentenceCodes.const _) hworld
    exact convergesTo_iff_asympEq_const.mpr
      (hei.trans (convergesTo_iff_asympEq_const.mp (lic_limitingBelief_tendsto P DP hworld ψ)))
  · have hei := lic_expectation_indicator_unconditional P DP (fun _ => ∼ψ)
      (MachineSentenceCodes.const _) hworld
    have h := convergesTo_iff_asympEq_const.mpr
      (hei.trans (convergesTo_iff_asympEq_const.mp (lic_limitingBelief_tendsto P DP hworld (∼ψ))))
    rwa [show limitingBelief P (∼ψ) = 1 - limitingBelief P ψ by linarith] at h
  · rw [max_lt_iff]; constructor <;> linarith
  · rw [lt_min_iff]; constructor <;> linarith

end Cleanroom.Li.LiCoupledPair.B
