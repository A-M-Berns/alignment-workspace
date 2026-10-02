/-
  `dp-learner-nr` target 10: diagonal ε-exploration is FAF's paradox resistance; prices are
  single-valued.

  The only file importing `LogicalInduction` besides `LeakLI.lean`; kept separate so that a slice
  kill costs one file.
-/

import LogicalInduction.Properties.Introspection
import LogicalInduction.Properties.Coherence

open LO
open LogicalInduction
open scoped LogicalInduction
open Filter Topology

namespace Cleanroom.Decision.DpLearnerNr

/-! ## (a) Soto's exploration sentence is FAF's diagonal -/

/-- **Soto's `S_n :≡ Q_n(S_n) < ε` is FAF's `ParadoxResistanceQuote.diagonal_reflected` at
`p := ε`**, and its price is asymptotically `ε`: `lic_paradox_resistance` instantiated. The row's
content is the *identification* of the exploration sentence with FAF's diagonal — Soto's fn. 10:
the agent explores on day `n` iff the sentence saying "my price for exploring today is below
`ε`" is true, and paradox resistance makes that price `ε`.
Source: Soto 2023 PIBBSS report §3.1.1 and fn. 10 (`research/references/bli/soto-2023/`,
`pdftotext` ll. 399–440: the diagonal exploration sentence); [[bli-soto-b-inventory]] 029;
FAF `LogicalInduction/Properties/Introspection.lean` (`ParadoxResistanceQuote`,
`lic_paradox_resistance`, `thm:lp`); [[dp-learner-nr-mandate]] target 10(a)
Kind: L
Fidelity: exact (one instantiation; the package `q` is FAF's object, constructed by FAF under
`Construction/Quotation` — `lic_paradox_resistance_ofDiagonal_unconditional` — not instantiated
here, see the report)
Hyps: (a) FAF's `IsLogicalInductor`, the package `q`, `hworld` -/
theorem soto_exploration_price (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (ε : ℚ) (h0 : 0 < ε) (h1 : ε < 1) (q : ParadoxResistanceQuote P DP ε)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (q.sentence n)) ≈ₙ fun _ => (ε : ℝ) :=
  lic_paradox_resistance P DP ε h0 h1 q hworld

/-- **The unpredictability gloss**: the exploration sentence's price is eventually strictly
between `0` and `1` — `Q` cannot predict its own exploration rounds with certainty, because the
price is `ε`, neither `0` nor `1`. ("Predictable to stronger predictors" is prose — findings.)
Source: Soto 2023 PIBBSS report §3.1.1 ("the agent cannot predict when it will explore");
[[bli-soto-b-inventory]] 029; [[dp-learner-nr-mandate]] target 10(a)
Kind: L
Fidelity: exact (of the corollary)
Hyps: (a) as in `soto_exploration_price` -/
theorem soto_exploration_unpredictable (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (ε : ℚ) (h0 : 0 < ε) (h1 : ε < 1)
    (q : ParadoxResistanceQuote P DP ε)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ᶠ n in atTop, 0 < P n (q.sentence n) ∧ P n (q.sentence n) < 1 := by
  have h := soto_exploration_price P DP ε h0 h1 q hworld
  have ht : Tendsto (fun n => P n (q.sentence n) - (ε : ℝ)) atTop (𝓝 0) := h
  have hε0 : (0 : ℝ) < ε := by exact_mod_cast h0
  have hε1 : (ε : ℝ) < 1 := by exact_mod_cast h1
  have hη : 0 < min (ε : ℝ) (1 - ε) := lt_min hε0 (by linarith)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp ht) _ hη
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have hd := hN n hn
  rw [Real.dist_eq, sub_zero, abs_lt] at hd
  have hm1 : min (ε : ℝ) (1 - ε) ≤ ε := min_le_left _ _
  have hm2 : min (ε : ℝ) (1 - ε) ≤ 1 - ε := min_le_right _ _
  constructor <;> linarith [hd.1, hd.2]

/-! ## (b) Bunthut's spread: a price is a number, and it converges -/

/-- **Prices converge** (the substantive LI fact behind "the market has a single price"): for an
inductor, every sentence's price sequence converges to some limit — FAF's `lic_price_convergesTo`
(`thm:con`), instantiated. That a price is *a number* is by type: FAF's
`History := ℕ → Valuation`, `Valuation := Sentence → ℝ` (a `D`-level remark, no theorem); the
reading of the Bunthut thread and of Abram's market-maker reply (post 13 l. 769) is
ATTRIBUTION-UNVETTED.
Source: `sl-workflow/posts/13-…md` l. 769 (the market-maker reply; ATTRIBUTION-UNVETTED);
[[dp-sl-2-inventory]] 075; FAF `LogicalInduction/Properties/Coherence.lean` (`lic_price_convergesTo`,
`thm:con`); [[faf-map-li]] §3.2; [[dp-learner-nr-mandate]] target 10(b)
Kind: L
Fidelity: exact (instantiation)
Hyps: (a) FAF's `IsLogicalInductor`, `hworld` -/
theorem price_converges (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : Sentence) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ L : ℝ, ConvergesTo (fun n => P n φ) L :=
  lic_price_convergesTo P DP φ hworld

end Cleanroom.Decision.DpLearnerNr
