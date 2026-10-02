/-
  Kripke countermodels for the non-provability claims.

  Targets 4 and 7(b) of [[dp-troll-bridge-mandate]], the non-vacuity witnesses for the schema
  of target 3, and the semantic form of target 1(d). Every `GL ⊬ φ` here is a Kripke model on
  a frame checked against `Frame.IsGL` (transitive, converse well-founded), refuting `φ` at a
  world, transported through Foundation's `Sound Modal.GL FrameClass.GL` instance — except
  the Proposition 10 family (`provable_crosser_not_afflicted`, `top_not_afflicted`,
  `tiling_not_afflicted_provable`, `dispositional_respect_two_cases`), which is syntactic:
  a reduction to FAF's `unprovable_box_bot` (repair round 1).

  Frames: Foundation's `blackpoint` (one dead-end world), `chainFrame` (`w0 ≺ w1`) and
  `chain3Frame` (`w0 ≺ w1 ≺ w2`).
-/

import Cleanroom.Decision.DpTrollBridge.Basic
import ModalAgents.GL
import Foundation.Modal.Kripke.Logic.GL.Soundness

open LO LO.Modal
open LO.Entailment LO.Modal.Entailment

namespace Cleanroom.Decision.DpTrollBridge

/-! ## Refutation through soundness -/

/-- A world of a GL frame (transitive, converse well-founded) that fails `φ` under some
valuation refutes `GL ⊢ φ`, by Foundation's soundness of `Modal.GL` for `FrameClass.GL`.
Source: none: infrastructure (Foundation `Sound Modal.GL Kripke.FrameClass.GL`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma unprovable_of_countermodel {φ : Modal.Formula ℕ} (F : Kripke.Frame) (hF : F.IsGL)
    (V : Kripke.Valuation F) (x : F.World)
    (hx : ¬ Formula.Kripke.Satisfies ⟨F, V⟩ x φ) : Modal.GL ⊬ φ := fun h => by
  have hmem : F ∈ Kripke.FrameClass.GL := hF
  have hnot := Kripke.iff_not_validOnFrameClass_exists_valuation_world.mpr ⟨F, hmem, V, x, hx⟩
  exact hnot (LO.Sound.sound (𝓜 := Kripke.FrameClass.GL) h)

/-! ## Frames -/

/-- The two-world chain `w0 ≺ w1` (worlds `0`, `1` of `Fin 2`): at `w0` the logic is
consistent (`∼□⊥`) but `□□⊥` holds; `w1` is a dead end (`□⊥`).
Source: [[dp-troll-bridge-mandate]] target 4 ("a two-world Kripke model")
Kind: D
Fidelity: n/a
Hyps: n/a -/
def chainFrame : Kripke.Frame := ⟨Fin 2, fun x y => x = 0 ∧ y = 1⟩

instance chainFrame_trans : IsTrans _ chainFrame.Rel := ⟨by
  intro a b c h₁ h₂
  simp only [chainFrame] at h₁ h₂ ⊢
  obtain ⟨rfl, rfl⟩ := h₁
  obtain ⟨h, -⟩ := h₂
  exact absurd h (by decide)⟩

instance chainFrame_irrefl : Std.Irrefl chainFrame.Rel := ⟨by
  intro a h
  simp only [chainFrame] at h
  obtain ⟨rfl, h⟩ := h
  exact absurd h (by decide)⟩

instance chainFrame_finite : Finite chainFrame.World := inferInstanceAs (Finite (Fin 2))

instance chainFrame_decEq : DecidableEq chainFrame.World := inferInstanceAs (DecidableEq (Fin 2))

/-- The two-world chain is a GL frame.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
instance chainFrame_isGL : chainFrame.IsGL := {}

/-- The accessibility relation of the two-world chain, as a `simp` lemma (the frame is never
unfolded in proofs: unfolding it to a literal defeats the keyed `IsGL` instance and trips a
Foundation instance cycle).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
@[simp] lemma chainFrame_rel (x y : chainFrame.World) :
    chainFrame.Rel x y ↔ x = (0 : Fin 2) ∧ y = (1 : Fin 2) := Iff.rfl

/-- The three-world chain `w0 ≺ w1 ≺ w2` (worlds of `Fin 3`, `x ≺ y` iff `x < y`).
Source: [[dp-troll-bridge-mandate]] target 4 ("three-world (chain) frame")
Kind: D
Fidelity: n/a
Hyps: n/a -/
def chain3Frame : Kripke.Frame := ⟨Fin 3, fun x y => x < y⟩

instance chain3Frame_trans : IsTrans _ chain3Frame.Rel := ⟨by
  intro a b c h₁ h₂
  simp only [chain3Frame] at h₁ h₂ ⊢
  exact lt_trans h₁ h₂⟩

instance chain3Frame_irrefl : Std.Irrefl chain3Frame.Rel := ⟨by
  intro a h
  simp only [chain3Frame] at h
  exact lt_irrefl _ h⟩

instance chain3Frame_finite : Finite chain3Frame.World := inferInstanceAs (Finite (Fin 3))

/-- The three-world chain is a GL frame.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
instance chain3Frame_isGL : chain3Frame.IsGL := {}

/-- The root `w0` of the two-world chain.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def chainW0 : chainFrame.World := (0 : Fin 2)

/-- Valuation on the two-world chain making atom `b` true at `w0` only.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def chainValAt (b : ℕ) : Kripke.Valuation chainFrame := fun a w => a = b ∧ w = (0 : Fin 2)

/-- The all-false valuation on the two-world chain.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def chainValNone : Kripke.Valuation chainFrame := fun _ _ => False

/-- The root `w0` of the three-world chain.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def chain3W0 : chain3Frame.World := (0 : Fin 3)

/-- Valuation on the three-world chain making atom `b` true at `w0` and `w1` (not at `w2`).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def chain3ValBelowTop (b : ℕ) : Kripke.Valuation chain3Frame :=
  fun a w => a = b ∧ w ≠ (2 : Fin 3)

/-- Valuation on Foundation's one-point frame making atom `b` true.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def pointValAt (b : ℕ) : Kripke.Valuation Kripke.blackpoint := fun a _ => a = b

/-- The all-false valuation on the one-point frame.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def pointValNone : Kripke.Valuation Kripke.blackpoint := fun _ _ => False

/-! ## Non-vacuity of the schema (target 3) -/

/-- **N+ witness for the schema: the boxed schema at an atom is consistent *with
consistency*.** `GL ⊬ ⊡(H b) 🡒 □⊥`: on the two-world chain `w0 ≺ w1` with every atom false,
`⊡(H b)` holds at `w0` (`∼b` holds everywhere, so `H b` does) while `□⊥` fails at `w0`. So the
schema's hypothesis is satisfiable at a world where the logic is consistent, and there the
conclusion `∼b` of `stays_schema` is exercised — not true for the dead-end reason `□⊥` —
while neither `b` nor `∼b` is provable (`atom_unprovable`, `neg_atom_unprovable`). Replaces
the round-0 witness `boxdotH_atom_consistent` (now a corollary), which lived at Foundation's
one-point dead end, where both conclusions of the schema theorems hold for the trivial
reason. The same fact is the tiling step for a provable crosser
(`tiling_not_afflicted_provable`).
Source: [[dp-troll-bridge-mandate]] target 3 trap (iii); repair round 1 (fidelity N1, adversarial N4)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem boxdotH_atom_con (b : ℕ) :
    Modal.GL ⊬ (⊡(H (.atom b : Modal.Formula ℕ)) 🡒 □⊥) :=
  unprovable_of_countermodel chainFrame chainFrame_isGL chainValNone chainW0
    (by simp [Formula.Kripke.Satisfies, chainValNone, chainW0, H]; try decide)

/-- The boxed schema at an atom is consistent, `GL ⊬ ∼⊡(H b)`: a corollary of
`boxdotH_atom_con` (round 0 proved it on the one-point frame; the two-world witness is the
stronger fact).
Source: [[dp-troll-bridge-mandate]] target 3 trap (iii)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem boxdotH_atom_consistent (b : ℕ) :
    Modal.GL ⊬ ∼(⊡(H (.atom b : Modal.Formula ℕ))) := fun h =>
  boxdotH_atom_con b (by cl_prover [h])

/-! ## Target 4: Proposition 10 and the two-agent picture -/

/-- **Proposition 10 (a causal agent is not afflicted), GL form.** The doc's proof: 𝔅 crosses
by its rule, so `Cross_𝔅` is a true Σ₁ sentence and `T ⊢ Cross_𝔅`; were `T ⊢ Cross_𝔅 → □⊥`,
then `T ⊢ □⊥`, a false Σ₁ sentence, against Σ₁-soundness. In GL: for any *provable* crossing
sentence `c`, `GL ⊬ c 🡒 □⊥`, since `GL ⊢ c` and `GL ⊢ c 🡒 □⊥` would give `GL ⊢ □⊥`, refuted
by FAF's `unprovable_box_bot` (Gödel's second theorem — the GL form of "T ⊬ □⊥", which is
what the doc's Σ₁-soundness is used for). The hypothesis `GL ⊢ c` is where the arithmetic
layer enters: the doc derives "T ⊢ Cross_𝔅" by Σ₁-completeness from the fact that 𝔅 crosses;
here it is assumed, not derived. Nothing links `c` to `□(c 🡒 …)`: 𝔅's non-responsiveness is
not modelled, only absent. This is the primary rendering of Proposition 10; the atom form
`causal_not_afflicted` (the mandate's) renders a different, undecided case.
Source: [[two-lesions-doc-2026-09-18]] §7 Proposition 10 and its proof; [[dp-core-inventory]] 082; [[dp-troll-bridge-mandate]] target 4; repair round 1 (fidelity B1)
Kind: P
Fidelity: variant: Σ₁-soundness is FAF's `unprovable_box_bot`; "T ⊢ Cross_𝔅" is a hypothesis
Hyps: (c) `hc : GL ⊢ c` stands for "T ⊢ Cross_𝔅, a true Σ₁ sentence" (Σ₁-completeness of the crossing sentence, not modelled) -/
theorem provable_crosser_not_afflicted {c : Modal.Formula ℕ} (hc : Modal.GL ⊢ c) :
    Modal.GL ⊬ (c 🡒 □⊥) := fun h => unprovable_box_bot (h ⨀ hc)

/-- Proposition 10 at the constant crosser `c := ⊤` (an agent that crosses no matter what):
`GL ⊬ ⊤ 🡒 □⊥`. The instance of `provable_crosser_not_afflicted` with no hypothesis left.
Source: [[two-lesions-doc-2026-09-18]] §7 Proposition 10 ("any agent that crosses receives 10")
Kind: L
Fidelity: exact (instance)
Hyps: (a) none -/
theorem top_not_afflicted : Modal.GL ⊬ ((⊤ : Modal.Formula ℕ) 🡒 □⊥) :=
  provable_crosser_not_afflicted verum!

/-- **An undecided atom is not afflicted** — the mandate's rendering of Proposition 10, kept
and relabelled. For an atom `b`, which GL neither proves nor refutes (`atom_unprovable`,
`neg_atom_unprovable`), `GL ⊬ b 🡒 □⊥`: countermodel `w0 ≺ w1` with `b` true at `w0`.
This is **not** the doc's case: there `Cross_𝔅` is T-decided (𝔅 provably crosses, or
provably stays — a halting computation) and the mechanism is Σ₁-soundness; here the atom is
undecided, and the fact holds in every normal modal logic (already in K: a reflexive point
with `b` true refutes it), so no property of GL, of Löb or of consistency is exercised. The
faithful GL form of Proposition 10 is `provable_crosser_not_afflicted`. What this lemma
renders is only the stipulation that no schema links `b` to `□(b 🡒 …)` (Known issue 3): a
coherent credence over a language naming the agent can leak the composite theorem into
`P(□⊥)` (the leak inequality belongs to `dp-learner-nr`).
Source: [[dp-troll-bridge-mandate]] target 4 (the atom rendering); [[two-lesions-doc-2026-09-18]] §7 Proposition 10 (contrast); [[dp-core-inventory]] 082; repair round 1 (fidelity B1)
Kind: L
Fidelity: variant: the atom is undecided where the doc's `Cross_𝔅` is T-decided; holds in K
Hyps: (c) the causal agent's action is an atom (no schema) — a stipulation, not derived -/
theorem causal_not_afflicted (b : ℕ) : Modal.GL ⊬ ((.atom b : Modal.Formula ℕ) 🡒 □⊥) :=
  unprovable_of_countermodel chainFrame chainFrame_isGL (chainValAt b) chainW0
    (by simp [Formula.Kripke.Satisfies, chainValAt, chainW0]; try decide)

/-- **The tiling path's "different program" step, atom form.** For the responsive agent's
atom `p` and a distinct atom `b` (the installed 𝔅's crossing), `GL ⊬ ⊡(H p) 🡒 (b 🡒 □⊥)`:
the schema for `p` says nothing about `b`. Same model, `p` false everywhere — so the
schema's consequent `∼p` holds throughout and the schema is never tested against its
antecedent (the countermodel refutes provability; it does not exercise the schema). The
expectation comparison `E[U | M] ≈ +10` is not formalized (recorded as `(c)` in the
findings). Stated for an *atom* `p`: at `p := □⊥` (the cross-first agent's formula) `⊡(H p)`
is refutable (`boxdotH_boxBot_refutable`) and the implication becomes provable; and `p ≠ b`
is necessary (at `p = b` the formula is `lobian_lesion_schema`). The provable-crosser form,
which is the doc's 𝔅, is `tiling_not_afflicted_provable`.
Source: [[non-responsiveness]] line 55 "(iii) Tiling"; [[dp-core-inventory]] 109; [[dp-troll-bridge-mandate]] target 4
Kind: P
Fidelity: weaker: the "different program" is a distinct undecided atom; the expectation step is absent
Hyps: (c) 𝔅's action is a distinct atom; (c) the value comparison is not modelled -/
theorem tiling_not_afflicted (p b : ℕ) (hpb : p ≠ b) :
    Modal.GL ⊬ (⊡(H (.atom p)) 🡒 ((.atom b : Modal.Formula ℕ) 🡒 □⊥)) :=
  unprovable_of_countermodel chainFrame chainFrame_isGL (chainValAt b) chainW0
    (by simp [Formula.Kripke.Satisfies, chainValAt, chainW0, H, hpb]; try decide)

/-- **The tiling step for a provable crosser** (the doc's 𝔅). For the responsive agent's
atom `p` and any *provable* crossing sentence `c` — in particular `⊤`, the constant crosser —
`GL ⊬ ⊡(H p) 🡒 (c 🡒 □⊥)`: the boxed schema at `p` is consistent with consistency
(`boxdotH_atom_con`), so it cannot make a provable crossing entail `□⊥`. This is
`provable_crosser_not_afflicted` under the responsive agent's schema; it needs no
distinctness hypothesis. The expectation comparison is not formalized.
Source: [[non-responsiveness]] line 55 "(iii) Tiling"; [[dp-core-inventory]] 109; [[dp-troll-bridge-mandate]] target 4; repair round 1 (fidelity B1 (iii))
Kind: P
Fidelity: weaker: the "different program" is a provable crosser; the expectation step is absent
Hyps: (c) `hc : GL ⊢ c` stands for "T ⊢ Cross_𝔅" (Σ₁-completeness, not modelled); (c) the value comparison is not modelled -/
theorem tiling_not_afflicted_provable (p : ℕ) {c : Modal.Formula ℕ} (hc : Modal.GL ⊢ c) :
    Modal.GL ⊬ (⊡(H (.atom p)) 🡒 (c 🡒 □⊥)) := fun h =>
  boxdotH_atom_con p (by cl_prover [h, hc])

/-- Dispositional T-respect, case (i): when the agent provably stays, `c 🡒 □⊥` is a theorem
for free (vacuously).
Source: [[non-responsiveness-learnability]] §3 lines 71–75; [[dp-core-2-inventory]] 044
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem lesion_of_neg {c : Modal.Formula ℕ} (h : Modal.GL ⊢ ∼c) : Modal.GL ⊢ c 🡒 □⊥ := by
  cl_prover [h]

/-- `GL ⊬ ∼b` for an atom: the one-world model with `b` true.
Source: [[dp-troll-bridge-mandate]] target 4
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem neg_atom_unprovable (b : ℕ) : Modal.GL ⊬ ∼(.atom b : Modal.Formula ℕ) :=
  unprovable_of_countermodel Kripke.blackpoint inferInstance (pointValAt b) ()
    (by simp [Formula.Kripke.Satisfies, pointValAt])

/-- `GL ⊬ b` for an atom: the one-world model with `b` false.
Source: [[dp-troll-bridge-mandate]] target 4
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem atom_unprovable (b : ℕ) : Modal.GL ⊬ (.atom b : Modal.Formula ℕ) :=
  unprovable_of_countermodel Kripke.blackpoint inferInstance pointValNone ()
    (by simp [Formula.Kripke.Satisfies, pointValNone])

/-- **Dispositional T-respect is never exercised against a non-vacuous proof (dp-core-2-044),
the two cases.** (i) If the agent provably stays (`GL ⊢ ∼c`), a proof of the lesion
`c 🡒 □⊥` exists, vacuously — the source's "T ⊢ ¬Cross_𝔅 (a halting computation), hence
T ⊢ Cross_𝔅 → □⊥ trivially — the theorem appears, is vacuous, and ignoring it changes
nothing". (ii) If the agent provably crosses (`GL ⊢ c`), no proof of the lesion exists
(`provable_crosser_not_afflicted`, Proposition 10) — the source's "while 𝔅 crosses, no
T-proof of Cross_𝔅 → □⊥ exists". Both cases are for an arbitrary formula `c`; the source's
`Cross_𝔅` is T-decided, so these are its two cases. Round 0 stated case (ii) for an
undecided atom (`⊬ ∼b` in place of `⊢ c`), which is neither case; that form is kept as
`dispositional_respect_undecided`.
Source: [[non-responsiveness-learnability]] §3 lines 71–75; [[dp-core-2-inventory]] 044; [[dp-troll-bridge-mandate]] target 4; repair round 1 (fidelity B1 (ii))
Kind: L
Fidelity: exact (of the two-case statement; the note's cost analysis is not modelled)
Hyps: (a) none -/
theorem dispositional_respect_two_cases :
    (∀ c : Modal.Formula ℕ, Modal.GL ⊢ ∼c → Modal.GL ⊢ c 🡒 □⊥) ∧
    (∀ c : Modal.Formula ℕ, Modal.GL ⊢ c → Modal.GL ⊬ (c 🡒 □⊥)) :=
  ⟨fun _ h => lesion_of_neg h, fun _ hc => provable_crosser_not_afflicted hc⟩

/-- The mandate's atom form of case (ii), kept for the record: for an undecided atom `b`,
`GL ⊬ b 🡒 □⊥` and `GL ⊬ ∼b`. This is neither of the source's two cases (there `Cross_𝔅`
is T-decided); see `causal_not_afflicted`.
Source: [[dp-troll-bridge-mandate]] target 4 (the atom rendering of case (ii)); repair round 1 (fidelity B1)
Kind: L
Fidelity: variant: the atom is undecided; neither of the source's cases
Hyps: (c) `b` atomic by fiat -/
theorem dispositional_respect_undecided (b : ℕ) :
    Modal.GL ⊬ ((.atom b : Modal.Formula ℕ) 🡒 □⊥) ∧ Modal.GL ⊬ ∼(.atom b : Modal.Formula ℕ) :=
  ⟨causal_not_afflicted b, neg_atom_unprovable b⟩

/-- **The unboxed schema does not suffice** (the mandate's trap (i)): `GL ⊬ H b 🡒 ∼b`.
Countermodel: the three-world chain with `b` true at `w0` and `w1`; at `w0`, `□(b 🡒 □⊥)`
fails (at `w1`, `b` holds and `□⊥` fails), so `H b` holds while `∼b` fails.
Source: [[dp-troll-bridge-mandate]] target 3 trap (i)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem H_alone_insufficient (b : ℕ) :
    Modal.GL ⊬ (H (.atom b : Modal.Formula ℕ) 🡒 ∼(.atom b : Modal.Formula ℕ)) :=
  unprovable_of_countermodel chain3Frame chain3Frame_isGL (chain3ValBelowTop b) chain3W0
    (by
      simp [Formula.Kripke.Satisfies, H, chain3Frame, chain3ValBelowTop, chain3W0]
      try decide)

/-! ## Target 7(b): the binding coin against the original troll — Löb stalls -/

/-- The pooled (binding-coin) agent's schema against the *original* troll: with
`cross := x ⋎ d` and `bad' := cross ⋏ □⊥`, `H'_d := □(cross 🡒 □⊥) 🡒 ∼d`. Only the
deliberate atom `d` is under the schema; the coin `x` is not. The headline is stated for
distinct atoms `x ≠ d`: that the coin is a *clean source* — its firing is not the deliberate
act and no schema links it to `□(… 🡒 …)` — enters exactly as `x ≠ d`.
Source: [[dp-troll-bridge-mandate]] target 7(b); [[troll-variants]] "The binding coin, again"
Kind: D
Fidelity: variant: credence abstraction
Hyps: (c) credence abstraction -/
def Hcoin (x d : ℕ) : Modal.Formula ℕ :=
  □((.atom x ⋎ .atom d : Modal.Formula ℕ) 🡒 □⊥) 🡒 ∼(.atom d)

/-- **Binding coin, original troll: Löb stalls.** `GL ⊬ ⊡(Hcoin x d) 🡒 ((x ⋎ d) 🡒 □⊥)`:
countermodel `w0 ≺ w1` with `x` true at `w0` and `d` false everywhere — the coin's crossing is
not deliberate, so the schema is satisfied while the crossing is safe. Contrast the
exploring-agent troll (`exploring_lesion`), where the troll also fires on `x` and Löb closes.
The dilemma/trap sorting of [[troll-variants]] is ATTRIBUTION-UNVETTED and not claimed here.
Source: [[troll-variants]] "The binding coin, again"; [[dp-core-inventory]] 112; [[dp-troll-bridge-mandate]] target 7(b)
Kind: N+
Fidelity: variant: credence abstraction
Hyps: (c) credence abstraction -/
theorem binding_coin_lob_stalls (x d : ℕ) (hxd : x ≠ d) :
    Modal.GL ⊬ (⊡(Hcoin x d) 🡒 ((.atom x ⋎ .atom d : Modal.Formula ℕ) 🡒 □⊥)) :=
  unprovable_of_countermodel chainFrame chainFrame_isGL (chainValAt x) chainW0
    (by simp [Formula.Kripke.Satisfies, chainValAt, chainW0, Hcoin, hxd.symm]; try decide)

/-! ## Target 1(d), semantic form -/

/-- The height-1 countermodel for the odd ordering's Löb sentence: at `w0` of `w0 ≺ w1`,
`∼□⊥ ⋏ □□⊥` holds and `□⊥` fails, so `GL ⊬ (∼□⊥ ⋏ □□⊥) 🡒 □⊥` — the semantic form of
`odd_lesion_unprovable`.
Source: `sl-workflow/notes/repair/P11.md` P11-6′(a) ("Löb's hypothesis fails at world 1"); [[dp-troll-bridge-mandate]] target 1(d)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem height_one_countermodel :
    Modal.GL ⊬ ((∼□⊥ ⋏ □□⊥ : Modal.Formula ℕ) 🡒 □⊥) :=
  unprovable_of_countermodel chainFrame chainFrame_isGL chainValNone chainW0
    (by simp [Formula.Kripke.Satisfies, chainW0]; try decide)

end Cleanroom.Decision.DpTrollBridge
