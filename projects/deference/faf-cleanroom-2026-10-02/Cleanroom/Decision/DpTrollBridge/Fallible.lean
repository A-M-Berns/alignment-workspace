/-
  The fallible troll: a troll that fires with probability `q` when triggered.

  Target 8 of [[dp-troll-bridge-mandate]]. The doc's step through (β) — `E[U | Cross] =
  10 − 20q < 0` — holds iff `q > ½`; at the modal level this is a *metatheoretic* case split on
  a rational `q`: for `q > ½` the schema is `H c` and the lesion follows; for `q ≤ ½` the schema
  is `⊤` and a provable crosser (or an undecided atom) is not afflicted. The expectation
  arithmetic is outside GL and is disclosed as `(c)`; the two headlines are instantiations by
  construction of `Hq` (Kind T — recorded, not headlines in the sense of [[STANDARDS]] §6).
  The bounded-agent half of the doc's paragraph (`□_M`) is out of type for FAF and is
  recorded in the findings only.
-/

import Cleanroom.Decision.DpTrollBridge.Lesion
import Cleanroom.Decision.DpTrollBridge.Countermodels

open LO LO.Modal
open LO.Entailment LO.Modal.Entailment

namespace Cleanroom.Decision.DpTrollBridge

/-- The fallible troll's schema at trigger probability `q`: the credence step of Lemma 8
(`E[U | Cross] = 10 − 20q < 0`) goes through iff `q > ½`, so the schema is `H c` for `q > ½`
and vacuous (`⊤`) otherwise. The case split is in the metatheory (a Lean `if` on `q : ℚ`);
the expectation arithmetic is not in GL, and the threshold is checked nowhere in Lean — this
definition makes both headlines below true by construction ([[STANDARDS]] §3's warning),
which is why they are graded `T`.
Source: [[two-lesions-doc-2026-09-18]] §7 "The fallible troll and the bounded agent"; [[dp-core-inventory]] 082; [[dp-troll-bridge-mandate]] target 8
Kind: D
Fidelity: variant: credence abstraction with the `q`-threshold placed in the metatheory
Hyps: (c) credence abstraction; (c) the threshold `q > ½` is imported from the doc's arithmetic, not derived -/
def Hq (q : ℚ) (c : Modal.Formula ℕ) : Modal.Formula ℕ :=
  if 1 / 2 < q then H c else ⊤

/-- For `q > ½` the fallible troll's schema *is* the original schema, by definition of `Hq`,
so `GL ⊢ ⊡(Hq q c) 🡒 (c 🡒 □⊥)` and `GL ⊢ ⊡(Hq q c) 🡒 ∼c` are `lobian_lesion_schema` and
`stays_schema` after `if_pos`.
Source: [[two-lesions-doc-2026-09-18]] §7 ("provided q > 1/2 … 𝔄 stays"); [[dp-troll-bridge-mandate]] target 8
Kind: T
Fidelity: variant: as `Hq` (an instantiation by construction)
Hyps: (c) credence abstraction; (c) threshold imported -/
theorem fallible_lesion_of_half_lt (q : ℚ) (hq : 1 / 2 < q) (c : Modal.Formula ℕ) :
    Modal.GL ⊢ ⊡(Hq q c) 🡒 (c 🡒 □⊥) ∧ Modal.GL ⊢ ⊡(Hq q c) 🡒 ∼c := by
  simp only [Hq, if_pos hq]
  exact ⟨lobian_lesion_schema c, stays_schema c⟩

/-- For `q ≤ ½` the schema is `⊤` by definition of `Hq`, and a *provable* crosser `c` (the
doc's "𝔄 crosses" — its crossing is then a true Σ₁ sentence, `T ⊢ Cross`) is not afflicted:
`GL ⊬ ⊡(Hq q c) 🡒 (c 🡒 □⊥)`, reducing to `provable_crosser_not_afflicted` (Proposition 10's
mechanism, Σ₁-soundness as `unprovable_box_bot`).
Source: [[two-lesions-doc-2026-09-18]] §7 ("For q ≤ 1/2 the step through (β) fails … and 𝔄 crosses"); [[dp-troll-bridge-mandate]] target 8; repair round 1 (fidelity B1 (iv))
Kind: T
Fidelity: variant: as `Hq`; the crossing is a provable sentence, as in Proposition 10
Hyps: (c) credence abstraction; (c) threshold imported; (c) `hc : GL ⊢ c` stands for "T ⊢ Cross" (Σ₁-completeness, not modelled) -/
theorem fallible_not_afflicted_of_le_half_provable (q : ℚ) (hq : q ≤ 1 / 2)
    {c : Modal.Formula ℕ} (hc : Modal.GL ⊢ c) :
    Modal.GL ⊬ (⊡(Hq q c) 🡒 (c 🡒 □⊥)) := by
  have hnot : ¬ (1 / 2 < q) := not_lt.mpr hq
  simp only [Hq, if_neg hnot]
  intro h
  apply provable_crosser_not_afflicted hc
  have ht : Modal.GL ⊢ (⊡(⊤ : Modal.Formula ℕ)) := ⟨K_intro verum (nec verum)⟩
  cl_prover [h, ht]

/-- The atom form of the `q ≤ ½` case, kept for the record: it inherits the atom rendering
of `causal_not_afflicted` (an *undecided* atom, which is not the doc's case — the doc's 𝔄
crosses and its crossing is T-provable; see `causal_not_afflicted`), and is degenerate by
construction (`Hq q b = ⊤`).
Source: [[two-lesions-doc-2026-09-18]] §7 ("For q ≤ 1/2 … 𝔄 crosses"); [[dp-troll-bridge-mandate]] target 8
Kind: T
Fidelity: variant: as `Hq`; inherits the undecided-atom rendering of `causal_not_afflicted`
Hyps: (c) credence abstraction; (c) threshold imported; (c) `b` atomic by fiat -/
theorem fallible_not_afflicted_of_le_half (q : ℚ) (hq : q ≤ 1 / 2) (b : ℕ) :
    Modal.GL ⊬ (⊡(Hq q (.atom b)) 🡒 ((.atom b : Modal.Formula ℕ) 🡒 □⊥)) := by
  have hnot : ¬ (1 / 2 < q) := not_lt.mpr hq
  simp only [Hq, if_neg hnot]
  intro h
  apply causal_not_afflicted b
  have ht : Modal.GL ⊢ (⊡(⊤ : Modal.Formula ℕ)) := ⟨K_intro verum (nec verum)⟩
  cl_prover [h, ht]

end Cleanroom.Decision.DpTrollBridge
