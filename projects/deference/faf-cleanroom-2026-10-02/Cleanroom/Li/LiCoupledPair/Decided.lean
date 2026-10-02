import Cleanroom.Li.LiCoupledPair.A.LedgerDecided
import Cleanroom.Li.LiCoupledPair.B.TieBreak
import Cleanroom.Found.LiQuoteLane.Ledger
import Cleanroom.Found.LiQuoteLane.OneWay
import Cleanroom.Found.LiQuoteLane.PaperWitness

/-!
# `li-coupled-pair` · Decided: T3 — ledger-decided ⟺ computable, and the ψ-tie-break

Reconciled module (namespace `Cleanroom.Li.LiCoupledPair`) for [[li-coupled-pair-mandate]] T3.
T3.1/T3.2 are angle A's (angle B did not attack them); T3.3 is angle B's (angle A did not attack
it). Each is restated once; the reconciler adds the N+ witness angle B's LI form lacked.

* **T3.1 (`ledgerDecided_iff_computable`).** Over `paperDP T`: a selector is ledger-decided along
  *some* computable selection family iff it is computable. Forward over *any* computable process
  (`computable_of_ledgerDecided`: dovetail `⟨j, s⟩` with `Nat.rfindOpt`); backward through FAF's
  `BooleanQuoteCode.ofComputable` (`A.selectorFamily`, `A.ledgerDecided_selectorFamily`,
  `A.ledgerDeterminedVia_selectorFamily`). Disclosure (findings F5): "computable from the ledger"
  is rendered "computable outright" — the published estimates are themselves computable in every
  instance of the run; the relativized form has no FAF carrier. N+ `altSel_ledgerDecided`.
  **Repair round 1 (audit r1, fidelity N1 / adversarial §3.2):** the iff's family is
  existentially quantified, and its `⟸` half is trivially witnessable — a family that encodes the
  answer with one fixed theorem and its negation (`S n j := if j = sel n then φ₀ else ∼φ₀`) is
  ledger-decided for *every* selector, computable or not (audit probe `TrivialSelectorFamily.lean`).
  The content of T3.1 is therefore the pair `computable_of_ledgerDecided` (forward, any computable
  process) + `A.ledgerDecided_selectorFamily` (the page's family `⌜sel n = j⌝`, backward); the iff
  is kept as the corollary the page states, Fidelity `variant`, and a dependent needing the page's
  biconditional for the option literals cites the pair, not the iff.
* **T3.2** is a finding (F6): `ledgerLuv_thresholdCodes` holds for every table — legality
  constrains the description, not the value. No theorem.
* **T3.3 (`psiTieBreak_finite`, `psiTieBreak_LI`).** The page's counterexample confirmed and
  strengthened: in every `PCWorld` the clairvoyant strategy is valued at `1` and the adversarial
  at `0` while the menu is valued at `𝟙_ψ`, `1 − 𝟙_ψ` (the expert never enters the per-world
  identities, so "no `½`" is right there); for any inductor with `ψ` undecided on both sides the
  expectations converge to `1` / `0` and strictly overshoot / undershoot the menu's limits. **The
  LI form is a `variant`, not `stronger` (repair round 1, audit r1 fidelity B1):** the page's
  rules are *tie-break rules of the argmax strategy* — with `P(ψ) = ½` the menu ties and the
  argmax set is `{1, 2}` — and the LI form drops the tie: with `ℙ∞ψ ≠ ½` the argmax set is a
  singleton and "select `O¹` iff `ψ`" is a world-dependent selector, not a tie-break. What the LI
  form proves is the page's F1-violation inequality in that general form; the tie-break reading
  needs `ℙ∞ψ = ½`, which no FAF theorem supplies (`limitingBelief` is a `limsup` nobody controls).
  Findings F-B5 rewritten accordingly. **New here:** the LI form's hypothesis package is inhabited
  over FAF's paper LIA by a fresh ledger-family atom (`paperDP_tieAtom_undecided`,
  `psiTieBreak_LI_paper`, N+), closing a non-vacuity gap of angle B's (its ledger row said "not
  instantiated here").
-/

namespace Cleanroom.Li.LiCoupledPair

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Cleanroom.Found.LiQuoteLane Filter Topology

/-! ## A. T3.1: ledger-decided ⟺ computable (angle A) -/

export Cleanroom.Li.LiCoupledPair.A (LedgerDecided LedgerDeterminedVia selTruth selectorCode
  selectorFamily altSel altSel_computable)

/-- **T3.1, forward: ledger-decided ⟹ computable, over any computable process.** If a computable
selection family `S` has, for every day, `S n (sel n)` entering some stage and no other option's
sentence ever entering, then `sel` is computable: dovetail `⟨j, s⟩` testing `S n j ∈ DP.D s`; by
uniqueness the first hit is `sel n`. "If the selection is always `Γ`-decided from the ledger,
enumerating proofs computes it." Angle A (`A.computable_of_ledgerDecided`). Scope: one-way.
Source: [[ledger-decided-tie-breaks]] §"Ledger-decided ⟺ computable from the ledger" (vq-wiki-023; lean-deference-074; lean-deference-2-019)
Kind: C
Fidelity: exact (with "from the ledger" rendered "computable outright"; findings F5)
Hyps: (a) none -/
theorem computable_of_ledgerDecided {DP : DeductiveProcess} {S : ℕ → ℕ → Sentence} {sel : ℕ → ℕ}
    (hDP : ComputableDeductiveProcess DP) (hS : Computable₂ S) (h : LedgerDecided DP S sel) :
    Computable sel :=
  A.computable_of_ledgerDecided hDP hS h

/-- **T3.1 (headline): ledger-decided ⟺ computable, over `paperDP T`.** A selector is
ledger-decided along *some* computable selection family iff it is computable. Backward: the
quotation family `S n j := ⌜sel n = j⌝` of FAF's `BooleanQuoteCode.ofComputable`
(`selectorFamily`), ledger-decided by `quote_positive_enters` / `quote_negative_refutes` (the
uniqueness half needs `[𝗣𝗔⁻ ⪯ T] [Consistent T]`: over an inconsistent `T` everything enters).
Angle A (`A.ledgerDecided_iff_computable`). Scope: one-way. **Statement weakness (repair round
1):** the family is existentially quantified, so the `⟸` half is trivially witnessable by a family
that encodes the answer with one fixed theorem and its negation (audit probe
`TrivialSelectorFamily.lean`); the backward content is `A.ledgerDecided_selectorFamily` (the
page's family `⌜sel n = j⌝`), the forward content `computable_of_ledgerDecided`. A dependent
needing the page's biconditional for the option literals cites that pair, not this iff.
Source: [[ledger-decided-tie-breaks]] §"Ledger-decided ⟺ computable from the ledger" (vq-wiki-023; lean-deference-074; lean-deference-2-019)
Kind: C
Fidelity: variant: the family is existentially quantified (its `⟸` half trivially witnessable); the page's family is `selectorFamily`, row `A.ledgerDecided_selectorFamily`; "from the ledger" rendered "computable outright" (F5)
Hyps: (a) none -/
theorem ledgerDecided_iff_computable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]
    (sel : ℕ → ℕ) [𝗣𝗔⁻ ⪯ T] [LO.Entailment.Consistent T] :
    (∃ S : ℕ → ℕ → Sentence, Computable₂ S ∧ LedgerDecided (paperDP T) S sel) ↔ Computable sel :=
  A.ledgerDecided_iff_computable T sel

/-- **N+ for T3.1:** the full hypothesis package of `computable_of_ledgerDecided` is inhabited
over `paperDP 𝗜𝚺₁` by the *non-constant* selector `altSel n := n % 2` with its computable
selection family — ledger-decided and ledger-determined — and `altSel 0 ≠ altSel 1`. Angle A
(`A.altSel_ledgerDecided`).
Source: mandate T3.1 (non-vacuity)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem altSel_ledgerDecided :
    LedgerDecided (paperDP 𝗜𝚺₁) (selectorFamily 𝗜𝚺₁ altSel altSel_computable) altSel ∧
      LedgerDeterminedVia (paperDP 𝗜𝚺₁) (selectorFamily 𝗜𝚺₁ altSel altSel_computable) altSel ∧
      Computable₂ (selectorFamily 𝗜𝚺₁ altSel altSel_computable) ∧ altSel 0 ≠ altSel 1 :=
  A.altSel_ledgerDecided

/-! ## B. T3.3: the ψ-tie-break counterexample (angle B) -/

export Cleanroom.Li.LiCoupledPair.B (clairvoyantRule adversarialRule menuTrue menuFalse
  clairvoyantStrategy adversarialStrategy)

/-- **T3.3, finite-exact:** in *every* `PCWorld` `v`, the clairvoyant rule's followed strategy
`Ŝ_c = 𝟙_{(ψ ⋏ ψ) ⋎ (∼ψ ⋏ ∼ψ)}` is valued at `1`, the adversarial `Ŝ_a = 𝟙_{(∼ψ ⋏ ψ) ⋎ (ψ ⋏ ∼ψ)}` at
`0`, and the menu `O¹ = 𝟙_ψ`, `O² = 𝟙_{∼ψ}` at `v.payout ψ`, `1 − v.payout ψ`. No `½`, no process.
Angle B (`B.psiTieBreak_finite`).
Source: [[ledger-decided-tie-breaks]] (lean-deference-074; lean-deference-2-019); mandate T3.3
Kind: N (finite-exact)
Fidelity: stronger: holds in every world with no `P(ψ) = ½` and no process; the products rendered propositionally
Hyps: (a) none -/
theorem psiTieBreak_finite (v : PCWorld) (ψ : Sentence) :
    v.ValuesAt (clairvoyantStrategy ψ) 1 ∧ v.ValuesAt (adversarialStrategy ψ) 0 ∧
      v.ValuesAt (menuTrue ψ) (v.payout ψ) ∧ v.ValuesAt (menuFalse ψ) (1 - v.payout ψ) :=
  B.psiTieBreak_finite v ψ

/-- **T3.3, LI form (stretch):** for any logical inductor `P` over `DP` with `ψ` undecided on
both sides stagewise, `𝔼_n(Ŝ_c) → 1`, `𝔼_n(Ŝ_a) → 0`, `𝔼_n(O¹) → ℙ∞(ψ)`, `𝔼_n(O²) → 1 − ℙ∞(ψ)`,
with the strict overshoot `max (ℙ∞ ψ) (1 − ℙ∞ ψ) < 1` and undershoot `0 < min …`. Composition of
FAF's `thm:ei`, `thm:provind`, `thm:lex` and `thm:nd`. Angle B (`B.psiTieBreak_LI`); N+
`psiTieBreak_LI_paper` below. **What the hypotheses carry:** `hworld` alone gives conjuncts 1–2
(the clairvoyant rule holds in every world, the adversarial in none); `hpos`/`hneg` enter only
through non-dogmatism, for the menu limits and the strict inequalities. **What is dropped
(repair round 1, audit r1 fidelity B1):** the page's tie. Its rules are tie-breaks of the argmax
strategy because `P(ψ) = ½` makes the menu tie (argmax set `{1, 2}`); here `ℙ∞ψ` is whatever the
inductor's `limsup` is, the argmax set is a singleton whenever `ℙ∞ψ ≠ ½`, and "select `O¹` iff
`ψ`" is then a world-dependent selector, not a tie-break. The conclusion is the page's
F1-violation inequality for such a selector; the tie-break reading needs `ℙ∞ψ = ½`, which no FAF
theorem supplies. The `½` is therefore not decoration (findings F-B5, rewritten).
Source: [[ledger-decided-tie-breaks]]; mandate T3.3 (LI form)
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
      0 < min (limitingBelief P ψ) (1 - limitingBelief P ψ) :=
  B.psiTieBreak_LI P DP ψ hworld hpos hneg

/-! ## C. N+ for the LI form: a fresh atom is undecided both ways by the paper process -/

/-- The undecided sentence of the witness: the ledger-family atom at payload `⟨0, ⟨0, ⌜0⌝⟩⟩`
(a fresh atom `paperDP 𝗜𝚺₁` never mentions).
Source: none: infrastructure (T3.3 witness)
Kind: D
Fidelity: n/a -/
abbrev tieAtom : Sentence := freshAtom ledgerFamily (ledgerPayload 0 0 (Encodable.encode (0 : ℚ)))

/-- **A fresh atom is undecided on both sides, stagewise, by `paperDP 𝗜𝚺₁`:** at every stage
there is a consistent world holding `tieAtom` and one holding `∼tieAtom`. Both worlds come from
li-quote-lane's `ledgerProcess_hworld` — the paper process extended by a ledger whose constant
table `1` affirms (resp. `0` denies) the threshold-`0` literal of item `0`, day `0`, same-day
publication — restricted to the paper stage, which the ledger process contains.
Source: mandate T3.3 ("`ψ` undecided on both sides"); [[ledger-decided-tie-breaks]]
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperDP_tieAtom_undecided :
    (∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) ∧ v.Holds tieAtom) ∧
      ∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) ∧ v.Holds (∼tieAtom) := by
  have hfree : ∀ a : ℕ → ℕ → ℚ,
      ProcessFreeOf (ledgerSchedule a (fun _ => PublicationSchedule.sameDay)) (paperDP 𝗜𝚺₁) :=
    fun _ => processFreeOf_ledgerSchedule_of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁)
  have key : ∀ (a : ℕ → ℕ → ℚ) (b : Bool), b = decide ((0 : ℚ) < a 0 0) → ∀ n,
      ∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) ∧
        v.Holds (literalOf (ledgerFamily, ledgerPayload 0 0 (Encodable.encode (0 : ℚ)), b)) := by
    intro a b hb n
    obtain ⟨v, hv⟩ := ledgerProcess_hworld (hfree a) (paperDP_hworld 𝗜𝚺₁)
      (max n (Encodable.encode (0 : ℚ)))
    refine ⟨v, fun φ hφ => hv φ ?_, hv _ ?_⟩
    · rw [ledgerProcess_D]
      exact Finset.mem_union_left _ ((paperDP 𝗜𝚺₁).mono_le (le_max_left _ _) hφ)
    · rw [ledgerProcess_D]
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, ?_, rfl⟩)
      rw [← ledgerSchedule_lits, ledgerSchedule_mem_iff]
      exact ⟨Nat.zero_le _, Nat.zero_le _, le_max_right _ _, Nat.zero_le _, hb⟩
  refine ⟨fun n => ?_, fun n => ?_⟩
  · obtain ⟨v, hv, hh⟩ := key (fun _ _ => (1 : ℚ)) true (decide_eq_true zero_lt_one).symm n
    exact ⟨v, hv, by simpa [literalOf_true] using hh⟩
  · obtain ⟨v, hv, hh⟩ := key (fun _ _ => (0 : ℚ)) false (decide_eq_false (lt_irrefl _)).symm n
    exact ⟨v, hv, by simpa [literalOf_false] using hh⟩

/-- **T3.3, LI form, N+ witness:** the full hypothesis package of `psiTieBreak_LI` is inhabited
by FAF's paper LIA `liaHistory (paperDP 𝗜𝚺₁)` over `paperDP 𝗜𝚺₁` at the fresh atom `tieAtom`:
there, `𝔼_n(Ŝ_c) → 1`, `𝔼_n(Ŝ_a) → 0`, the menu converges to `ℙ∞(tieAtom)`, `1 − ℙ∞(tieAtom)`, and
the overshoot/undershoot are strict. Non-degenerate: the atom is genuinely undecided both ways
(`paperDP_tieAtom_undecided`), the inductor is FAF's real construction. Nothing is claimed about
the value of `ℙ∞(tieAtom)`; in particular not that it is `½` (the page's tie), see
`psiTieBreak_LI`.
Source: mandate T3.3 (non-vacuity); [[ledger-decided-tie-breaks]]
Kind: N+
Fidelity: variant (as `psiTieBreak_LI`: the tie dropped)
Hyps: (a) none -/
theorem psiTieBreak_LI_paper :
    ConvergesTo (fun n => (clairvoyantStrategy tieAtom).expect (liaHistory (paperDP 𝗜𝚺₁)) n) 1 ∧
      ConvergesTo (fun n => (adversarialStrategy tieAtom).expect (liaHistory (paperDP 𝗜𝚺₁)) n) 0 ∧
      ConvergesTo (fun n => (menuTrue tieAtom).expect (liaHistory (paperDP 𝗜𝚺₁)) n)
        (limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) tieAtom) ∧
      ConvergesTo (fun n => (menuFalse tieAtom).expect (liaHistory (paperDP 𝗜𝚺₁)) n)
        (1 - limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) tieAtom) ∧
      max (limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) tieAtom)
        (1 - limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) tieAtom) < 1 ∧
      0 < min (limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) tieAtom)
        (1 - limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) tieAtom) := by
  haveI : IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) :=
    LIA_is_logical_inductor _ (paperDP_computable 𝗜𝚺₁)
  exact B.psiTieBreak_LI (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) tieAtom (paperDP_hworld 𝗜𝚺₁)
    paperDP_tieAtom_undecided.1 paperDP_tieAtom_undecided.2

end Cleanroom.Li.LiCoupledPair
