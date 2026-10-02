import Cleanroom.Deference.DefArgmaxValue.Punishing
import Cleanroom.Deference.DefArgmaxValue.Witness
import Cleanroom.Deference.DefArgmaxValue.TruthTeller

/-!
# `def-argmax-value` · Open: the world-only predicate of record, and the one stated-open
conjecture (targets 12a–12b; repair round 2)

* `WorldOnly` (12a, the predicate of record, syntactic: no threshold sentence of any option
  carries a quotation atom — payload tag `2`, FAF's `sentenceAtomCodes_quoteAtom`) with its N+
  `worldOnly_atomMenu`. The two conjectures stated OPEN over it until repair round 2 —
  `condStableOn_of_worldOnly` (H3 is a theorem on world-only menus; vq-wiki-017 /
  lean-deference-073) and `selfOpaque_perIndex` (2-026's per-index gap vanishes there) — are
  **refuted as stated** (`WorldOnlyRefuted.lean`, audit r2 adversarial B2): a liar rebuilt
  through `T`'s theorem lane (payload tag `paperPrimeTag = 5`, FAF's `schemaArgClaimSentence` at
  `universalQuotePos`) is syntactically world-only, and on it H3 fails
  (`condStableOn_of_worldOnly_refuted`) and the per-index gap tends to `−(1 − s)s`
  (`selfOpaque_perIndex_refuted`). The predicate stays as the definition of record — inhabited
  (`worldOnly_atomMenu`), and refuted as a sufficient condition. The honest conjecture needs the
  complexity clause the sources state ("below the produce-hardness of `A`'s quotes") and no
  payload-tag test can express it: tag `5` carries both ordinary arithmetic and, through
  `universalQuotePos`, the market's own decisions; FAF has no object for it (F19). The round-1
  diagnosis named the computation-claim lane (tags `0`/`1`); that lane cannot carry a liar —
  FAF's halting lane publishes a halting claim when `T` proves it and refutes only *bounded*
  halting claims, so it lacks the Π₁ direction a liar needs (audit r2 adversarial N1).
* `punishing_masses_interior` was stated OPEN here until repair round 1 (`PunishingTie.lean`).
* **`truthPrice_frequently_interior`** — the one open statement of the package after repair
  round 2 (audit r2 fidelity N1): does FAF's inductor keep the truth-teller's price
  `P_{f n}(τ_n)` frequently interior? By `truth_masses_interior_iff_price_interior`
  (`TruthTeller.lean`) this is exactly "the truth-teller is an interior-mass inhabitant of
  `CondStableOn`" — open problem 3 (F23) on the only candidate menu the package's vocabulary
  has left (F24). Nothing proved in the package decides it either way.
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows
open Cleanroom.Deference.DefSqueezeDiamond
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
variable (f : DeferralFunction) (s : ℚ)

/-- **World-only menus** (12a, the predicate of record): no threshold sentence of any option
contains a quotation atom (payload tag `2`). Syntactic and, per threshold, decidable
(`Finset` membership). **Refuted as a sufficient condition for H3** (`WorldOnlyRefuted.lean`):
it does not exclude the theorem lane (tag `5`), through which the market's own decisions are
reflected just as through the quotation atoms; the honest definition needs a complexity clause
FAF has no object for (see the module docstring).
Source: vq-wiki-017; lean-deference-073; mandate target 12a
Kind: D
Fidelity: weaker: syntactic only (no complexity-class clause); refuted as sufficient for H3 -/
def WorldOnly {k : ℕ} (M : Menu k) : Prop :=
  ∀ (j : Fin (k + 1)) (n : ℕ) (r : ℚ), ∀ a ∈ sentenceAtomCodes ((M.O j n).gt r), a.unpair.1 ≠ 2

/-- The atom family `Formula.atom ⟨0, n⟩`: e.c., and never a quotation atom. Payload tag `0` is,
in FAF's global allocation table (`Construction/Knowledge/Syntax.lean`,
`ComputationClaimKind.godelCode .halting = 0`), the halting-claim tag, so these are syntactically
computation-claim atoms (malformed or genuine), which `theoremDP` may publish (audit r2
adversarial N4); nothing here depends on whether it does.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def plainAtom (n : ℕ) : Sentence := LO.Propositional.Formula.atom (Nat.pair 0 n)

/-- The plain atoms are e.c.
Source: none: infrastructure (FAF `machineSentenceCodes_atom`)
Kind: L
Fidelity: n/a -/
theorem plainAtom_codes : MachineSentenceCodes plainAtom :=
  (machineSentenceCodes_atom.comp ((UnaryRuler.const 0).pair UnaryRuler.id)).of_eq (fun n => rfl)

/-- **The N+ of `WorldOnly`**: the two-option menu of the literal indicators of two e.c.
non-quotation atom families (`⟨0, n⟩` and `⟨0, n+1⟩`, tag `0` — FAF's halting-claim tag) is
world-only. (Whether `paperDP T` decides these atoms — which would make the menu eventually
constant in value — is not examined; the N+ shows the *syntactic* predicate is inhabited, which
is all the row claims. Audit r1 N7, r2 N4.) To be read with `foMenu_worldOnly`: the predicate is
inhabited *and* refuted as sufficient for H3.
Source: mandate target 12 trap ("ship one world-only, non-constant menu" — "non-constant" not
verified)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
def atomMenu : Menu 1 :=
  twoOptionMenu (fun n => literalIndicator (plainAtom n)) (fun n => literalIndicator (plainAtom (n + 1)))
    (literalIndicator_machineThresholdCodeSeq plainAtom_codes)
    (literalIndicator_machineThresholdCodeSeq (plainAtom_codes.comp UnaryRuler.id.succ))

/-- The atom menu is world-only.
Source: mandate target 12 trap
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem worldOnly_atomMenu : WorldOnly atomMenu := by
  intro j n r a ha
  have key : ∀ m, ∀ a ∈ sentenceAtomCodes ((literalIndicator (plainAtom m)).gt r), a.unpair.1 ≠ 2 := by
    intro m a ha
    simp only [literalIndicator] at ha
    split_ifs at ha
    · simp at ha
    · simp only [plainAtom, sentenceAtomCodes_atom, Finset.mem_singleton] at ha
      subst ha
      simp
    · simp at ha
  fin_cases j
  · exact key n a ha
  · exact key (n + 1) a ha

/-- **OPEN — the truth-teller's price stays frequently interior** (open problem 3 on the
truth-teller menu; audit r2 fidelity N1): `∃ c > 0, ∃ᶠ n, c ≤ P_{f n}(τ_n) ≤ 1 − c`, with
`τ_n ↔ s_{f n} ≤ P_{f n}(τ_n)` (`truthSentence_holds_iff`). Equivalent
(`truth_masses_interior_iff_price_interior`) to "the self-prediction masses on `truthMenu` stay
interior", i.e. to the truth-teller being an interior-mass inhabitant of `CondStableOn` — H3
holds there for every package (`condStableOn_truth_any_package`), with surplus `p_n(1 − p_n)`
(`truth_h3_surplus`). Truth value unknown: the truth-teller is a fixed point with positive
feedback, and `P_{f n}(τ_n) → 1` (`τ_n` eventually always true) and `→ 0` (eventually always
false) are each consistent with everything proved in the package. Not attempted.
Source: audit r2 fidelity N1; F23 (open problem 3); [[total-trust-implies-value]] §Necessity
Kind: OPEN
Fidelity: exact (the question as posed)
Hyps: n/a (open) -/
theorem truthPrice_frequently_interior (_hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s)
    (_hs1 : s < 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ n in atTop,
      c ≤ (liaHistory (paperDP T)) (f n) (truthSentence T f s hs0.le n) ∧
        (liaHistory (paperDP T)) (f n) (truthSentence T f s hs0.le n) ≤ 1 - c := by
  sorry

end

end Cleanroom.Deference.DefArgmaxValue
