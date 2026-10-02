import Cleanroom.Li.LiDiagonal.Paper
import Cleanroom.Deference.DefObstruction.Core
import Cleanroom.Deference.DefObstruction.FragmentWitness

/-!
# `def-obstruction` · ChiParadox: the settlement-level χ-paradox is not an exploitation theorem (S1)

The inventory's proposed "well-posed core of 2b" (anson-005's extension flag): *if the trader
class contains a trader computing the market's day-`n` price on `C_n`, and the process settles
`C_n` to `𝟙[A_n(C_n) ≤ ½]`, then the market is exploited.* Over FAF every `EF` trader reads the
market's day-`n` price, so the first clause is automatic, and the second clause at `<` is FAF's
`ParadoxResistanceQuote` at `p = ½` (`diagonal_reflected : v.Holds (χ_n) ↔ P_n(χ_n) < ½`). FAF's
`thm:lp` (`lic_paradox_resistance`) proves such markets are **not** exploited — they are
inductors with `P_n(χ_n) → ½` — and `li-diagonal` exhibits one: FAF's LIA over `paperDP 𝗜𝚺₁`
with its Kleene diagonal at `½` (`harmonicDiagonalQuote`). So the `<` form of the proposed core
is **refuted** (`chiParadox_refuted`, resting on the positive statement
`paperLIA_half_diagonal_inductor`), and the price is pinned, not exploited
(`chiParadox_price_tendsto_half`).

**Which form is whose (repair round 1, audit B1).** anson-005's own sentence is written at `≤`
(`𝟙[A_n(C_n) ≤ ½]`, the ledger's tie polarity, `gDiag`'s); the `<` form refuted here is this
package's *variant* of it, the one FAF's `ParadoxResistanceQuote` states. The proposal's own `≤`
form is **not** shown false: it is the OPEN `le_diagonal_inductor_exists` (`Open.lean`),
conjectured to go the same way. The refutation is a fortiori for the bare `<`-proposal:
`ParadoxResistanceQuote` carries *more* than the proposal's diagonal clause (two affine
certificates), so a universal over the smaller class failing refutes the universal over the
larger one.

**Why the refuted universal carries a satisfiable-stage guard (repair round 2, adversarial B1).**
The round-1 statement quantified over every `DeductiveProcess`. Over FAF that universal is false
for a reason the proposal never intended: a process with one unsatisfiable stage makes **every**
computable market a logical inductor (`isLogicalInductor_of_stage_unsatisfiable`, the paper's
`thm:scon`), and empties every completed-world quantifier — including the quote's
`diagonal_reflected` clause — so a `ParadoxResistanceQuote` over it is available by the very
constructor the real witness uses (`QuotationTheoryPresentation.mono` lifts the paper's
presentation to any process whose stages contain the paper's). § B keeps that degenerate witness
on record (`unsatDP`, `chiParadox_unguarded_degenerate`): the paper process with the obstruction
atom adjoined in *both* polarities, no `thm:lp` and no paper market needed. The refuted universal
now carries `∀ n, ∃ v, v.ConsistentWith (DP.D n)` as an antecedent — exactly as
`chiParadox_price_tendsto_half`, FAF's `lic_paradox_resistance` and the OPEN
`le_diagonal_inductor_exists` carry it — and `unsatDP` cannot witness it (`unsatDP_fails_guard`);
the paper witness does, at the cost of `paperDP_hworld 𝗜𝚺₁`.

This is exactly what [[self-referential-settlement-target]] §2.3 says: at the *sentence* level
the diagonal is benign; 2a's content is the *cross-process* settlement (the reader's process
settles against the *publisher's* number, a hard `0/1` the publisher's market cannot clear), and
2b's content needs that entanglement plus a resource model — neither is a single-market fact
(findings F-ChiParadox). The `≤` form (ties settle true, the ledger's polarity) is `Open.lean`'s
`le_diagonal_inductor_exists`: a `≤`-diagonal quote package is not an FAF object, and prices of
negations agree only asymptotically, so it is not a one-line variant.

Scope: single-market.
-/

namespace Cleanroom.Deference.DefObstruction

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
open Cleanroom.Li.LiDiagonal
open Filter Topology

/-! ## A. The refutation, over processes with satisfiable stages -/

/-- **The positive statement the refutation rests on**: the paper process has satisfiable stages,
FAF's LIA over it carries a `½`-diagonal (`ParadoxResistanceQuote`, by `li-diagonal`'s
`harmonicDiagonalQuote` on `paperQuotationPresentation`/`paperMarketComputation`), and it is a
logical inductor over the paper process (`paperLIA`). The content of `chiParadox_refuted` is in
this statement rather than in a proof term (repair round 2, adversarial B1).
Scope: single-market.
Source: LI `thm:lp` (the construction it is about); [[self-referential-settlement-target]] §2.3 (LI-χ); mandate S1
Kind: C (FAF's construction, li-diagonal's quote, FAF's inductor theorem)
Fidelity: exact (FAF's objects throughout; strict tie convention is FAF's)
Hyps: (a) none -/
theorem paperLIA_half_diagonal_inductor :
    (∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n)) ∧
      Nonempty (ParadoxResistanceQuote (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) (1 / 2)) ∧
      IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) :=
  ⟨paperDP_hworld 𝗜𝚺₁,
    ⟨harmonicDiagonalQuote (paperQuotationPresentation 𝗜𝚺₁) (paperMarketComputation 𝗜𝚺₁)
      (1 / 2)⟩,
    paperLIA 𝗜𝚺₁⟩

/-- **The settlement-level χ-paradox at `<` is not an exploitation theorem**: it is false that
every market with a `½`-diagonal (`ParadoxResistanceQuote P DP ½`) over a process with
satisfiable stages fails the criterion. Witness: `paperLIA_half_diagonal_inductor` — FAF's LIA
over the paper process with its Kleene diagonal at `½`. The satisfiable-stage antecedent is the
one FAF's `lic_paradox_resistance` carries; without it the statement is true for a trivial
reason (§ B, `chiParadox_unguarded_degenerate`).
Scope: single-market.
Source: anson-005 (extension flag: the proposed "well-posed core" of 2b, written at `≤`); [[self-referential-settlement-target]] §2.3 (LI-χ: the sentence-level diagonal is benign); mandate S1
Kind: C
Fidelity: variant: strict tie convention (`<`) in place of the proposal's `≤`; the proposal's own `≤` form is OPEN (`le_diagonal_inductor_exists`). The refuted universal ranges over processes with satisfiable stages (the guard `thm:scon` makes necessary — repair round 2); stronger as a refutation of the bare `<`-proposal in that FAF's `ParadoxResistanceQuote` carries two affine certificates beyond the diagonal clause, so the universal ranges over a smaller quote class
Hyps: (a) none -/
theorem chiParadox_refuted :
    ¬ (∀ (P : History) (DP : DeductiveProcess),
        (∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) →
        (∃ _q : ParadoxResistanceQuote P DP (1 / 2), True) → ¬ IsLogicalInductor P DP) := by
  intro h
  obtain ⟨hworld, ⟨hq⟩, hind⟩ := paperLIA_half_diagonal_inductor
  exact h _ _ hworld ⟨hq, trivial⟩ hind

/-- **What the settlement-level `<`-diagonal does to an inductor**: its price tends to `½`
(FAF's `thm:lp`). Pinned, not exploited.
Scope: single-market.
Source: LI `thm:lp`; [[self-referential-settlement-target]] §2.3 (LI-χ); mandate S1
Kind: L (instance of FAF's `lic_paradox_resistance`)
Fidelity: exact
Hyps: (a) none -/
theorem chiParadox_price_tendsto_half (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (q : ParadoxResistanceQuote P DP (1 / 2))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (q.sentence n)) ≈ₙ fun _ => (1 / 2 : ℝ) := by
  have h := lic_paradox_resistance P DP (1 / 2) (by norm_num) (by norm_num) q hworld
  simpa using h

/-! ## B. Why the guard: the unguarded universal is refuted by an inconsistent process

Adopted from audit r2's probe `ChiParadoxDegenerate` (adversarial B1). `unsatDP` is the paper
process with the obstruction atom `freshAtom 5 0` adjoined in both polarities, so every stage is
unsatisfiable; by FAF's `thm:scon` every computable market is an inductor over it, and every
`ConsistentWithTheory` quantifier over it is vacuous. Nothing below is imported by anything
else; it is the record of why `chiParadox_refuted` carries its first antecedent. -/

/-- **The inconsistent process**: the paper process with the obstruction atom adjoined in both
polarities — every stage contains `freshAtom 5 0` and `∼ freshAtom 5 0`.
Scope: single-market (the encoding check).
Source: audit r2 probe `ChiParadoxDegenerate`; LI `thm:scon`
Kind: D
Fidelity: n/a (the degenerate witness's own object)
Hyps: n/a -/
noncomputable def unsatDP : DeductiveProcess := extendBy paperAdjoin (atomSchedule 5 0 false)

/-- The inconsistent process is computable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem unsatDP_computable : ComputableDeductiveProcess unsatDP :=
  extendBy_ofList_computable paperAdjoin_computable _ _ (Primrec.const _)

/-- The positive literal is in every stage.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem unsatDP_pos_mem (n : ℕ) : freshAtom 5 0 ∈ unsatDP.D n := by
  unfold unsatDP
  rw [extendBy_D]
  exact Finset.mem_union_left _ (adjoinAtom_mem (paperDP 𝗜𝚺₁) 5 0 n)

/-- The negative literal is in every stage.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem unsatDP_neg_mem (n : ℕ) : (∼ freshAtom 5 0) ∈ unsatDP.D n := by
  unfold unsatDP
  rw [extendBy_D]
  apply Finset.mem_union_right
  rw [Finset.mem_image]
  exact ⟨(5, 0, false), by simp [atomSchedule], literalOf_false 5 0⟩

/-- **Every stage of the inconsistent process is unsatisfiable.**
Source: audit r2 probe `ChiParadoxDegenerate`
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem unsatDP_unsat (n : ℕ) : ∀ v : PCWorld, ¬ v.ConsistentWith (unsatDP.D n) := by
  intro v hv
  have h1 := hv _ (unsatDP_pos_mem n)
  have h2 := hv _ (unsatDP_neg_mem n)
  rw [PCWorld.holds_neg] at h2
  exact h2 h1

/-- Hence there is no completed world: every `ConsistentWithTheory unsatDP` quantifier is
vacuous — so is `ParadoxResistanceQuote.diagonal_reflected` over it.
Source: audit r2 probe `ChiParadoxDegenerate`
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem unsatDP_no_theory_world : ∀ v : PCWorld, ¬ v.ConsistentWithTheory unsatDP :=
  fun v hv => unsatDP_unsat 0 v (hv 0)

/-- **The inconsistent process fails the guard** of `chiParadox_refuted`.
Source: audit r2 probe `ChiParadoxDegenerate`
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem unsatDP_fails_guard : ¬ (∀ n, ∃ v : PCWorld, v.ConsistentWith (unsatDP.D n)) :=
  fun h => by obtain ⟨v, hv⟩ := h 0; exact unsatDP_unsat 0 v hv

/-- **Every computable market is a logical inductor over the inconsistent process** (FAF's
`isLogicalInductor_of_stage_unsatisfiable`, the paper's `thm:scon`).
Source: LI `thm:scon`; audit r2 probe `ChiParadoxDegenerate`
Kind: L (instance of FAF's theorem)
Fidelity: exact
Hyps: (a) none -/
theorem unsatDP_every_market_inductor (V : History) (hV : ComputableMarket V) :
    IsLogicalInductor V unsatDP :=
  isLogicalInductor_of_stage_unsatisfiable V unsatDP hV unsatDP_computable (unsatDP_unsat 0)

/-- The paper stages sit inside the inconsistent process's stages.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem paperDP_subset_unsatDP (k : ℕ) : (paperDP 𝗜𝚺₁).D k ⊆ unsatDP.D k := by
  intro x hx
  unfold unsatDP paperAdjoin adjoinAtom
  rw [extendBy_D, extendBy_D]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)

/-- FAF's quotation presentation of the paper process, lifted to the inconsistent process
(`QuotationTheoryPresentation.mono`: every field is theory-side or "enters some stage").
Source: none: infrastructure (FAF `QuotationTheoryPresentation.mono`)
Kind: D
Fidelity: n/a -/
noncomputable def unsatQ : QuotationTheoryPresentation unsatDP 𝗜𝚺₁ :=
  (paperQuotationPresentation 𝗜𝚺₁).mono paperDP_subset_unsatDP
    (Classical.choice unsatDP_computable.nonemptyComputation)

/-- A `ParadoxResistanceQuote` at `½` over the inconsistent process, by the package's own
constructor (`li-diagonal`'s `harmonicDiagonalQuote`); its `diagonal_reflected` clause is vacuous
(`unsatDP_no_theory_world`).
Source: audit r2 probe `ChiParadoxDegenerate`
Kind: D
Fidelity: n/a -/
noncomputable def unsatQuote : ParadoxResistanceQuote (liaHistory unsatDP) unsatDP (1 / 2) :=
  harmonicDiagonalQuote unsatQ (liaMarketComputation unsatDP unsatDP_computable) (1 / 2)

/-- **The round-1 (unguarded) statement of `chiParadox_refuted`, proved by the degenerate
witness**: no `thm:lp`, no paper market — an inconsistent process and any computable market over
it (`thm:scon`). This is why the headline carries its satisfiable-stage antecedent; it is not a
headline and carries no claim about the proposal.
Scope: single-market (the encoding check).
Source: audit r2 probe `ChiParadoxDegenerate` (adversarial B1); [[STANDARDS]] §3 (impossibility results get a check that the result isn't an artifact of the encoding)
Kind: N− (degenerate witness of the unguarded universal's negation: an inconsistent process)
Fidelity: n/a (the statement it refutes is the one the package no longer claims)
Hyps: (a) none -/
theorem chiParadox_unguarded_degenerate :
    ¬ (∀ (P : History) (DP : DeductiveProcess),
        (∃ _q : ParadoxResistanceQuote P DP (1 / 2), True) → ¬ IsLogicalInductor P DP) :=
  fun h => h _ _ ⟨unsatQuote, trivial⟩
    (unsatDP_every_market_inductor _ (liaMarketComputation unsatDP unsatDP_computable).toComputable)

end Cleanroom.Deference.DefObstruction
