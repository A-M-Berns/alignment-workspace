import Cleanroom.Bli.BliFound.StateSentence
import Cleanroom.Bli.BliFound.PaperInstances

/-!
# `bli-found` · Unlinked: B1's fresh state atom forces nothing about quotes

**The claim.** The mandate's D5 says linkage is "true of the B2 encoding, false by construction
for B1". `StateSentence.lean` proves the first half (`LNKcell_stateSentence`); this file proves
the second, in its honest form: B1's fresh atom `stateAtom m q` is **free** over `paperDP T` —
every completed-theory world can be overridden to make it true while agreeing with the original
world on every non-fresh atom (`stateAtom_free`) — and therefore **linkage for the fresh atom
collapses to unconditional forcing**: `LNKcell stateAtom (quoteAt T) S cellOf (paperDP T)` holds
iff every quote it is supposed to force is forced in every completed-theory world anyway
(`lnkcell_stateAtom_iff_unconditional`). The fresh atom adds nothing. That is the B1-vs-B2
contrast: B2's state sentence forces the state's own cell (`LNKcell_stateSentence`); B1's atom
forces only what was forced already.

**What is *not* a contrast.** `LNKcell` at the constant cell `(2, 3)` — a cell no price lies in —
fails for *any* state-sentence family that some completed-theory world holds
(`lnkcell_fails_at_impossible_cell`), B1's fresh atom (`lnkcell_stateAtom_fails_at_impossible_cell`)
and B2's `stateSentence` on the T7 witness system (`lnkcell_stateSentence_fails_at_impossible_cell`)
alike. Continuation 1 shipped the B1 instance under the name `stateAtom_unlinked` and called it
"B1 is unlinked"; audit round 1 (fidelity B1, adversarial N1) showed the test does not
discriminate, and the name, docstring and ledger row were corrected in repair round 1.

**`Constraints.LNK` is refutable.** The first pass's closed-interval linkage predicate, paired
with the package's own `quoteAt T`, is false for **every** state system over `paperDP T`
(`lnk_quoteAt_refutable`): at `lo = hi` the interval quote is a propositional contradiction, and
the three cases (`S.val` below, at, above the exact quote of `⊥`) each contradict
`quoteLuv_valuesAt` in a world holding the fresh atom (from `stateAtom_free`). Findings F-13.

The override world is `Extend.override` for the one-literal schedule `{(stateFamily, ⟨m, q⟩, true)}`;
it is consistent with every stage of `paperDP T` because no stage mentions a run atom
(`paperDP_cleanroomFree`), by the first pass's conservativity machinery
(`extendBy_consistentWithTheory`, `PCWorld.consistentWithTheory_union_left`).

Sources: mandate D5 (`LNK`: "false by construction for B1"); [[bli-program]] §2.3; audit r1
(fidelity B1/B2, adversarial N1/N2, probes 2, 3, P1, P7).
-/

namespace Cleanroom.Bli.BliFound

open LogicalInduction LO.Propositional

/-- The one-literal schedule asserting the state atom of `(m, q)` at every stage.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def stateAtomSchedule (m q : ℕ) : LiteralSchedule where
  lits _ := {(stateFamily, Nat.pair m q, true)}
  mono _ := Finset.Subset.refl _

/-- The one-literal schedule is functional.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateAtomSchedule_functional (m q : ℕ) : (stateAtomSchedule m q).Functional := by
  intro s f p ⟨_, hneg⟩
  simp [stateAtomSchedule] at hneg

section

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁]

/-- **B1's state atom is free over `paperDP T`.** Every completed-theory world `v₀` of
`paperDP T` has an override `v` that is still a completed-theory world, holds `stateAtom m q`,
and agrees with `v₀` on every atom outside the schedule's (in particular on every atom any
stage of `paperDP T` mentions, and on every quotation atom).
Source: mandate D5 (`LNK`: "false by construction for B1"); T3 conservativity
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem stateAtom_free (m q : ℕ) (v₀ : PCWorld) (hv₀ : v₀.ConsistentWithTheory (paperDP T)) :
    ∃ v : PCWorld, v.ConsistentWithTheory (paperDP T) ∧ v.Holds (stateAtom m q) ∧
      ∀ a, a ∉ (stateAtomSchedule m q).atoms → (v a ↔ v₀ a) := by
  have hL := stateAtomSchedule_functional m q
  have hfree : ProcessFreeOf (stateAtomSchedule m q) (paperDP T) :=
    ProcessFreeOf.of_cleanroomFree (paperDP_cleanroomFree T) _
  refine ⟨override (stateAtomSchedule m q) v₀, ?_, ?_, ?_⟩
  · exact PCWorld.consistentWithTheory_union_left (extendBy_consistentWithTheory hL hfree hv₀)
  · have := override_holds_literal hL v₀ (s := 0)
      (x := (stateFamily, Nat.pair m q, true)) (by simp [stateAtomSchedule])
    simpa [literalOf_true, stateAtom] using this
  · intro a ha
    exact override_agree _ _ ha

variable [𝗥₀ ⪯ T]

/-- Every interval quote of the market's own quote code is a conjunction of tag-`2` atoms, hence
tag-free for every run tag.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma quoteAt_tagFree (m : ℕ) (φ : Sentence) (lo hi : ℚ) {t : ℕ} (ht : cleanroomBaseTag ≤ t) :
    TagFreeSentence t (quoteAt T m φ lo hi) := by
  have hgt : ∀ r : ℚ, TagFreeSentence t ((quoteLuv T m φ).gt r) := by
    intro r a ha
    have h2 := sentenceAtomCodes_quoteAtom
      (Nat.pair (marketQuoteCode T).code (Nat.pair (Nat.pair m (Encodable.encode φ))
        (Encodable.encode r))) a ha
    simp only [cleanroomBaseTag] at ht
    omega
  exact (hgt lo).and (hgt hi).neg

/-- **B1 linkage collapses to unconditional forcing.** Over `paperDP T`, `LNKcell` for the fresh
state atom holds iff every quote it is supposed to force is forced in every completed-theory
world anyway: the fresh atom adds nothing. Forward direction: `stateAtom_free` gives a world
holding the atom that agrees with the given one off the fresh atom, and the interval quote (a
conjunction of tag-`2` atoms, `quoteAt_tagFree`) transports back across the override
(`PCWorld.holds_congr_atomCodes`). This is the honest content of D5's "false by construction for
B1": not that some cell assignment fails (that is true of B2 too, `lnkcell_fails_at_impossible_cell`),
but that B1's atom never forces more than the empty antecedent does.
Source: mandate D5 (`LNK`: "false by construction for B1"); audit r1 (fidelity B1, probe 2)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem lnkcell_stateAtom_iff_unconditional (S : StateSystem)
    (cellOf : ℕ → ℕ → Sentence → ℚ × ℚ) :
    LNKcell stateAtom (quoteAt T) S cellOf (paperDP T) ↔
      ∀ m, ∀ q ∈ S.states m, ∀ φ ∈ smallSet m, ∀ v : PCWorld,
        v.ConsistentWithTheory (paperDP T) →
          v.Holds (quoteAt T m φ (cellOf m q φ).1 (cellOf m q φ).2) := by
  constructor
  · intro h m q hq φ hφ v₀ hv₀
    obtain ⟨v, hv, hatom, hagree⟩ := stateAtom_free T m q v₀ hv₀
    have hq' := h m q hq φ hφ v hv hatom
    have hfree : FreeOf (stateAtomSchedule m q)
        (quoteAt T m φ (cellOf m q φ).1 (cellOf m q φ).2) :=
      FreeOf.of_tagFree fun f _ => quoteAt_tagFree T m φ _ _ (Nat.le_add_right _ f)
    exact (PCWorld.holds_congr_atomCodes _ fun a ha => hagree a (hfree a ha)).mp hq'
  · intro h m q hq φ hφ v hv _
    exact h m q hq φ hφ v hv

/-- **`LNKcell` fails at an impossible cell for any held state sentence** — not a B1-vs-B2
contrast. If some completed-theory world of `paperDP T` holds `σ m (S.actual m)`, then `LNKcell`
for `σ` fails at the constant cell `(2, 3)`, because every price lies in `[0, 1]`
(`le_of_holds_quoteAt`, `paperQuote_mem`) and `⊥` is small on every day.
Source: audit r1 (fidelity B1, adversarial N1, probes 1/P1)
Kind: L
Fidelity: n/a (no source claim; the generic form of the two N− instances below)
Hyps: (a) -/
theorem lnkcell_fails_at_impossible_cell (σ : ℕ → ℕ → Sentence) (S : StateSystem) (m : ℕ)
    (hσ : ∃ v : PCWorld, v.ConsistentWithTheory (paperDP T) ∧ v.Holds (σ m (S.actual m))) :
    ¬ LNKcell σ (quoteAt T) S (fun _ _ _ => ((2 : ℚ), (3 : ℚ))) (paperDP T) := by
  intro hlnk
  obtain ⟨v, hv, hσ⟩ := hσ
  have hq := hlnk m (S.actual m) (S.actual_mem m) ⊥ (falsum_mem_smallSet m) v hv hσ
  have hle := le_of_holds_quoteAt T v hv hq
  have hmem := paperQuote_mem T m ⊥
  linarith [hle.1, hmem.2]

variable [𝗣𝗔⁻ ⪯ T] [LO.Entailment.Consistent T]

/-- The B1 instance: `LNKcell` for the fresh atom fails at the cell `(2, 3)`, for every state
system. **Not B1-specific** — the same test refutes B2
(`lnkcell_stateSentence_fails_at_impossible_cell`); the B1-specific statement is
`lnkcell_stateAtom_iff_unconditional`. Continuation 1 shipped this as `stateAtom_unlinked`
("B1 is unlinked"); renamed in repair round 1.
Source: mandate D5; audit r1 (fidelity B1)
Kind: N−
Fidelity: weaker: a refutation at a cell no price lies in; not B1-specific
Hyps: (a) -/
theorem lnkcell_stateAtom_fails_at_impossible_cell (S : StateSystem) (m : ℕ) :
    ¬ LNKcell stateAtom (quoteAt T) S (fun _ _ _ => ((2 : ℚ), (3 : ℚ))) (paperDP T) := by
  refine lnkcell_fails_at_impossible_cell T stateAtom S m ?_
  obtain ⟨v₀, hv₀⟩ := paperDP_nonvacuous T
  obtain ⟨v, hv, hatom, -⟩ := stateAtom_free T m (S.actual m) v₀ hv₀
  exact ⟨v, hv, hatom⟩

/-- **`Constraints.LNK` with the package's own quotes is refutable for every state system.**
With `lo = hi` the interval quote is `⌜Q > lo⌝ ⋏ ∼⌜Q > lo⌝`, a propositional contradiction; so
`LNK` (every closed interval containing `S.val`) paired with `quoteAt T` fails for every `S`, not
only "at the boundary": the three cases are `S.val 0 (S.actual 0) ⊥` below, at, or above the
market's exact quote of `⊥`, each contradicting `quoteLuv_valuesAt` in a completed-theory world
holding the fresh atom (`stateAtom_free`).
Source: findings F-13; audit r1 (fidelity B2, probe 3; adversarial N2, probe P7)
Kind: P
Fidelity: exact (refutation of the definition of record `Constraints.LNK` at `quoteAt T`)
Hyps: (a) -/
theorem lnk_quoteAt_refutable (S : StateSystem) : ¬ LNK (quoteAt T) S (paperDP T) := by
  intro h
  obtain ⟨v₀, hv₀⟩ := paperDP_nonvacuous T
  obtain ⟨v, hv, hatom, -⟩ := stateAtom_free T 0 (S.actual 0) v₀ hv₀
  obtain ⟨-, -, hval⟩ := quoteLuv_valuesAt T 0 ⊥ v hv
  have key : ∀ lo hi : ℚ, (lo : ℝ) ≤ S.val 0 (S.actual 0) ⊥ → S.val 0 (S.actual 0) ⊥ ≤ hi →
      v.Holds ((quoteLuv T 0 ⊥).gt lo) ∧ ¬ v.Holds ((quoteLuv T 0 ⊥).gt hi) := by
    intro lo hi hlo hhi
    have := h 0 (S.actual 0) (S.actual_mem 0) ⊥ (falsum_mem_smallSet 0) lo hi hlo hhi v hv hatom
    rw [quoteAt, PCWorld.holds_and, PCWorld.holds_neg] at this
    exact this
  rcases lt_trichotomy (S.val 0 (S.actual 0) ⊥)
      ((paperQuote T 0 (Encodable.encode (⊥ : Sentence)) : ℚ) : ℝ) with hlt | heq | hgt
  · obtain ⟨hi, h1, h2⟩ := exists_rat_btwn hlt
    obtain ⟨lo, -, h3⟩ := exists_rat_btwn (sub_one_lt (S.val 0 (S.actual 0) ⊥))
    exact (key lo hi h3.le h1.le).2 ((hval hi).1 h2)
  · have := key _ _ heq.ge heq.le
    exact this.2 this.1
  · obtain ⟨lo, h1, h2⟩ := exists_rat_btwn hgt
    obtain ⟨hi, h3, -⟩ := exists_rat_btwn (lt_add_one (S.val 0 (S.actual 0) ⊥))
    exact (hval lo).2 h1 (key lo hi h2.le h3.le).1

end

/-- The B2 instance of the impossible-cell test on the T7 witness system: the same constant cell
`(2, 3)` refutes `LNKcell` for `stateSentence` too (the actual table's sentence holds in every
completed-theory world, `actualCode_holds`). With `lnkcell_stateAtom_fails_at_impossible_cell`
this shows the test does not separate B1 from B2.
Source: audit r1 (fidelity probe 1, adversarial P1)
Kind: N−
Fidelity: weaker: a refutation at a cell no price lies in; not B2-specific
Hyps: (a) -/
theorem lnkcell_stateSentence_fails_at_impossible_cell :
    ¬ LNKcell (stateSentence 𝗜𝚺₁ halfRound halfRound_computable) (quoteAt 𝗜𝚺₁) witnessSystem
      (fun _ _ _ => ((2 : ℚ), (3 : ℚ))) (paperDP 𝗜𝚺₁) := by
  refine lnkcell_fails_at_impossible_cell 𝗜𝚺₁ _ witnessSystem 0 ?_
  obtain ⟨v, hv⟩ := paperDP_nonvacuous 𝗜𝚺₁
  exact ⟨v, hv, actualCode_holds 0 v hv⟩

end Cleanroom.Bli.BliFound
