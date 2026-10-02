import Cleanroom.Decision.DpTrollBridge.Lesion
import Cleanroom.Decision.DpTrollBridge.Countermodels

/-!
# `dp-learner-nr` D1 and targets 1(d), 1(e), 8(b): the (β′) schema at the modal level

**D1.** Over `Modal.Formula ℕ`, `BetaPrime b r := (GL ⊢ b 🡘 r) ∧ (GL ⊢ r ∨ GL ⊢ ∼r)`: the agent's
crossing sentence is GL-equivalent to a formula `r` the theory *decides* — the rendering of
(β′), `T ⊢ Cross_𝔅 ↔ (Σ_w P₀(w)E(cross,w) > Σ_w P₀(w)E(stay,w))`, whose right-hand side is a
Δ₀ comparison of numerals and so is decided by T. A `(c)` modelling substitution: the
arithmetic layer is abstracted, and nothing in GL can express "the formula does not consult
`P(· | b)`", so NR1 is rendered by its *consequence* (decidedness of the comparison), not by its
form. The doc's (β) is `dp-troll-bridge`'s `H`.

**Target 1(d).** `betaPrime_decided`: a (β′) agent is decided; `betaPrime_crosser_not_afflicted`:
a (β′) agent whose comparison favours crossing is unafflicted — "Lemma 8's single use of (β) has
no counterpart under (β′)" is this theorem, by `dp-troll-bridge`'s
`provable_crosser_not_afflicted` (Proposition 10). **Trap (iii)**: the constant crosser `⊤` is a
`BetaPrime` agent (`r := ⊤`, `betaPrime_top`), so the note's "a constant crosser … negates (β)
without being NR1" is not a modal distinction (findings).

**Target 1(e).** The self-misprediction troll re-closes the trap: `dp-troll-bridge`'s
`exploring_lesion` with the exploration atom read as "crossed while `P_t(cross) < ½ + ε`".

**Target 8(b).** Conjecture F(v) per round: a round-indexed family of (β′) agents whose
comparison favours crossing at round `t` is unafflicted at round `t`, for every `t` — the
positive complement of `dp-troll-bridge`'s `policy_level_lesion`.
-/

open LO LO.Modal
open LO.Entailment LO.Modal.Entailment

namespace Cleanroom.Decision.DpLearnerNr

open Cleanroom.Decision.DpTrollBridge

/-- **D1 — the (β′) schema, modal level.** `BetaPrime b r`: the crossing sentence `b` is
GL-equivalent to `r`, and GL decides `r`. The arithmetic comparison
`Σ_w P₀(w)E(cross,w) > Σ_w P₀(w)E(stay,w)` with `P₀`, `E` numerals is Δ₀, so T proves it or its
negation; `r` stands for it. `r` need not mention `b` — nothing in GL can express "the formula
does not consult `P(·|b)`", so NR1 is rendered by its consequence (decidedness), not its form.
Source: [[non-responsiveness]] "NR1" ((β′)); [[non-responsiveness-learnability]] §1 NR1;
[[dp-core-2-inventory]] 038; [[dp-learner-nr-mandate]] D1
Kind: D
Fidelity: variant: the arithmetic layer abstracted to "GL decides `r`"
Hyps: (c) credence abstraction: the comparison is an arbitrary decided formula -/
def BetaPrime (b r : Modal.Formula ℕ) : Prop :=
  (Modal.GL ⊢ b 🡘 r) ∧ (Modal.GL ⊢ r ∨ Modal.GL ⊢ ∼r)

/-- A (β′) agent is decided: `GL ⊢ b` or `GL ⊢ ∼b`.
Source: [[non-responsiveness-learnability]] §0 ("Cross_𝔅 is a true Σ₁ sentence, so T proves
it" — the decided case); [[dp-learner-nr-mandate]] target 1(d)
Kind: L
Fidelity: exact
Hyps: (c) credence abstraction (D1) -/
theorem betaPrime_decided {b r : Modal.Formula ℕ} (h : BetaPrime b r) :
    Modal.GL ⊢ b ∨ Modal.GL ⊢ ∼b := by
  obtain ⟨hiff, hr | hnr⟩ := h
  · left; cl_prover [hiff, hr]
  · right; cl_prover [hiff, hnr]

/-- A (β′) agent whose comparison favours crossing provably crosses.
Source: [[dp-learner-nr-mandate]] target 1(d)
Kind: L -/
theorem betaPrime_crosses {b r : Modal.Formula ℕ} (h : BetaPrime b r) (hr : Modal.GL ⊢ r) :
    Modal.GL ⊢ b := by
  have hiff := h.1
  cl_prover [hiff, hr]

/-- **D1 collapses to decidedness**: `b` is a (β′) agent for *some* comparison `r` iff GL decides
`b` (take `r := b`). So in GL the comparison `r` carries no information beyond "GL decides `b`",
`betaPrime_decided` is an iff, and the modal (β′) rows are Proposition 10 relabelled
(`betaPrime_hyps_reduce`). This is the limit of the credence abstraction (c), stated so the
reader sees it; adopted from audit r1's `BetaPrimeCollapse` probe.
Source: [[dp-learner-nr-audit-r1-adversarial]] §3 item 3; [[dp-learner-nr-mandate]] D1
Kind: L
Hyps: (c) credence abstraction (D1) -/
theorem betaPrime_iff_decided (b : Modal.Formula ℕ) :
    (∃ r, BetaPrime b r) ↔ (Modal.GL ⊢ b ∨ Modal.GL ⊢ ∼b) := by
  constructor
  · rintro ⟨r, h⟩; exact betaPrime_decided h
  · intro h; exact ⟨b, by cl_prover, h⟩

/-- The hypothesis package of `betaPrime_crosser_not_afflicted` / `conjectureF_v_per_round` is
satisfiable for some `r` iff `GL ⊢ b`; the conclusion is then `provable_crosser_not_afflicted`.
Source: [[dp-learner-nr-audit-r1-adversarial]] §3 item 3; [[dp-learner-nr-mandate]] D1
Kind: L
Hyps: (c) credence abstraction (D1) -/
theorem betaPrime_hyps_reduce (b : Modal.Formula ℕ) :
    (∃ r, BetaPrime b r ∧ Modal.GL ⊢ r) ↔ Modal.GL ⊢ b := by
  constructor
  · rintro ⟨r, h, hr⟩; exact betaPrime_crosses h hr
  · intro hb; exact ⟨b, ⟨by cl_prover, Or.inl hb⟩, hb⟩

/-- **NR1 is (β′), not ¬(β)** (target 1(d)): a (β′) agent whose comparison favours crossing is
unafflicted — `GL ⊬ b 🡒 □⊥`. "Lemma 8's single use of (β) has no counterpart under (β′)": the
lesion needs the schema `H b = □(b 🡒 □⊥) 🡒 ∼b`, and a decided crosser refutes it by
Proposition 10 (`provable_crosser_not_afflicted`, Gödel 2).
Source: [[non-responsiveness]] "NR1" ("so Lemma 8's single use of (β) has no counterpart");
[[dp-core-2-inventory]] 038; [[two-lesions-doc-2026-09-18]] §7 Proposition 10;
[[dp-learner-nr-mandate]] target 1(d)
Kind: L (one cited fact, `provable_crosser_not_afflicted`, behind one `cl_prover` step; D1 adds no
theorem beyond Proposition 10 — `betaPrime_hyps_reduce`; relabelled from C at audit r1)
Fidelity: variant: credence abstraction (D1); the constant crosser `⊤` is also a (β′) agent
(`betaPrime_top`), so the note's "a constant crosser … negates (β) without being NR1" has no
modal rendering (findings)
Hyps: (c) credence abstraction (D1) -/
theorem betaPrime_crosser_not_afflicted {b r : Modal.Formula ℕ} (h : BetaPrime b r)
    (hr : Modal.GL ⊢ r) : Modal.GL ⊬ (b 🡒 □⊥) :=
  provable_crosser_not_afflicted (betaPrime_crosses h hr)

/-- A (β′) agent whose comparison favours staying provably stays, and then the lesion holds
vacuously (`dispositional_respect_two_cases` (i)).
Source: [[non-responsiveness-learnability]] §3 ("if `P₀(□⊥) ≥ ½` it stays, `T ⊢ ¬Cross_𝔅`,
and the theorem appears vacuously"); [[dp-learner-nr-mandate]] target 1(d)
Kind: L
Hyps: (c) credence abstraction (D1) -/
theorem betaPrime_stayer_vacuous_lesion {b r : Modal.Formula ℕ} (h : BetaPrime b r)
    (hnr : Modal.GL ⊢ ∼r) : Modal.GL ⊢ ∼b ∧ Modal.GL ⊢ (b 🡒 □⊥) := by
  have hnb : Modal.GL ⊢ ∼b := by
    have hiff := h.1
    cl_prover [hiff, hnr]
  exact ⟨hnb, dispositional_respect_two_cases.1 b hnb⟩

/-- **Trap (iii): the constant crosser is a (β′) agent** (`r := ⊤`). So "a constant crosser …
negate(s) (β) without being NR1" ([[non-responsiveness]]) is not renderable in GL: the
distinction lives in the arithmetic layer (a specific `P₀`).
Source: [[non-responsiveness]] "NR1" ("a constant crosser, a constant stayer and a coin all
negate (β)"); [[dp-learner-nr-mandate]] target 1 trap (iii)
Kind: N− (degenerate on purpose: it shows the modal rendering cannot separate the two)
Hyps: (c) credence abstraction (D1) -/
theorem betaPrime_top : BetaPrime (⊤ : Modal.Formula ℕ) ⊤ :=
  ⟨by cl_prover, Or.inl verum!⟩

/-- The constant stayer is a (β′) agent (`r := ⊥`), and satisfies `H ⊥` (so "negates (β)" is
not `⊬ H c` either: the modal (β) is a schema, not a biconditional with an expectation term).
Source: [[dp-learner-nr-mandate]] target 1 trap (iii)
Kind: N−
Hyps: (c) credence abstraction (D1) -/
theorem betaPrime_bot : BetaPrime (⊥ : Modal.Formula ℕ) ⊥ ∧ Modal.GL ⊢ H (⊥ : Modal.Formula ℕ) :=
  ⟨⟨by cl_prover, Or.inr (by cl_prover)⟩, by simp only [H]; cl_prover⟩

/-! ## Target 1(e): the self-misprediction troll re-closes the trap -/

/-- **The self-misprediction troll** (2-039's modal half): with the exploration atom `x` of
`dp-troll-bridge`'s exploring-agent schema read as "crossed while `P_t(cross) < ½ + ε`" (the
probabilistic trigger abstracted to an atom), a troll that fires on self-mispredicted crossings
makes every crossing bad under the boxed schema — Löb fires. This is `exploring_lesion x d`
instantiated; the row's content is the *reading* of `x`.
Source: [[non-responsiveness]] "NR2" ("a troll that fires on self-mispredicted crossing makes
the lemma hold for it and Löb fires"); [[non-responsiveness-learnability]] §8 B;
[[dp-core-2-inventory]] 039; [[dp-learner-nr-mandate]] target 1(e)
Kind: L
Fidelity: variant: the probabilistic trigger `P_t(cross) < ½ + ε` is an atom
Hyps: (c) credence abstraction; (c) the trigger is an atom -/
theorem self_misprediction_troll_lesion (x d : ℕ) :
    Modal.GL ⊢ ⊡(Hexp x d) 🡒 (exploringCross x d 🡒 exploringBad x d) :=
  exploring_lesion x d

/-- Under the self-misprediction troll the agent does not cross deliberately
(`exploring_deliberate_stays` instantiated).
Source: [[dp-learner-nr-mandate]] target 1(e)
Kind: L
Hyps: (c) credence abstraction; (c) the trigger is an atom -/
theorem self_misprediction_troll_stays (x d : ℕ) :
    Modal.GL ⊢ ⊡(Hexp x d) 🡒 ∼(.atom d) :=
  exploring_deliberate_stays x d

/-! ## Target 8(b): Conjecture F(v) per round -/

/-- **Conjecture F(v), per round** (target 8(b)): for a round-indexed family of crossing
sentences `cross t` and decided comparisons `r t` with `BetaPrime (cross t) (r t)`, at every
round whose comparison favours crossing the lesion `cross t 🡒 □⊥` is unprovable. This is
`provable_crosser_not_afflicted` at every `t`: the positive complement of `dp-troll-bridge`'s
`policy_level_lesion` — "relocation to the policy level changes nothing for (β), and the (β′)
agent is unafflicted at every round".
Source: [[policy-level-fdt-learner]] §6 Conjecture F (v) ("for every `t`, `T ⊬ (π_t = cross →
□⊥)` — Proposition 10 iterated"); [[marginal-formula-learner]] "Conjecture F"; [[dp-core-inventory]]
111(v); [[dp-core-2-inventory]] 046, 034's complement; [[dp-learner-nr-mandate]] target 8(b)
Kind: L (`provable_crosser_not_afflicted` at every `t`; relabelled from C at audit r1)
Fidelity: variant: credence abstraction (D1); "the trigger is a fact about `E`" is the
hypothesis that the comparison `r t` is decided. Note the source's (v) as printed ("for every
`t`, `T ⊬ (π_t = cross → □⊥)`") is false at a round where the decided agent *stays* — there
`T ⊢ ¬(π_t = cross)` and the lesion holds vacuously (`conjectureF_v_two_cases`); the theorem
here is the surviving form "at every crossing round" (findings F17)
Hyps: (c) credence abstraction (D1): `r t` is an arbitrary decided formula -/
theorem conjectureF_v_per_round (cross r : ℕ → Modal.Formula ℕ)
    (hβ' : ∀ t, BetaPrime (cross t) (r t)) :
    ∀ t, Modal.GL ⊢ r t → Modal.GL ⊬ (cross t 🡒 □⊥) :=
  fun t hr => betaPrime_crosser_not_afflicted (hβ' t) hr

/-- The two-case form per round: at every round the (β′) agent either provably crosses and
is unafflicted, or provably stays and the lesion `cross t 🡒 □⊥` is *provable* (vacuously). The
second disjunct is why the source's unqualified "for every `t`, `T ⊬ (π_t = cross → □⊥)`" needs
the qualifier "at every crossing round" (findings F17).
Source: [[policy-level-fdt-learner]] §6 Conjecture F (v); [[dp-learner-nr-mandate]] target 8(b)
Kind: L (case split over two cited facts; relabelled from C at audit r1)
Hyps: (c) credence abstraction (D1) -/
theorem conjectureF_v_two_cases (cross r : ℕ → Modal.Formula ℕ)
    (hβ' : ∀ t, BetaPrime (cross t) (r t)) :
    ∀ t, (Modal.GL ⊢ cross t ∧ Modal.GL ⊬ (cross t 🡒 □⊥)) ∨
      (Modal.GL ⊢ ∼(cross t) ∧ Modal.GL ⊢ (cross t 🡒 □⊥)) := by
  intro t
  rcases (hβ' t).2 with hr | hnr
  · exact Or.inl ⟨betaPrime_crosses (hβ' t) hr, betaPrime_crosser_not_afflicted (hβ' t) hr⟩
  · exact Or.inr (betaPrime_stayer_vacuous_lesion (hβ' t) hnr)

end Cleanroom.Decision.DpLearnerNr
