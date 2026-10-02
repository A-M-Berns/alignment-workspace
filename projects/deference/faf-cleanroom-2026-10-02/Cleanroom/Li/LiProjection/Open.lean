import Cleanroom.Li.LiProjection.LemmaA
import Cleanroom.Li.LiProjection.Marginal
import Cleanroom.Li.LiProjection.Fragments
import LogicalInduction.Construction.Primcodable
import LogicalInduction.Construction.Paper.TheoremDP
import LogicalInduction.Construction.LIA
import LogicalInduction.Properties.Conditioning
import Foundation.FirstOrder.Incompleteness.Halting

/-!
# `li-projection` · Open: the open statements of record (T3.3, the T6.1 target, T7)

Package `Cleanroom.Li.LiProjection` ([[li-projection-mandate]]), file 13 of the layout. Every
declaration here is stated precisely over FAF's objects and left with `sorry`; each is listed in
`li-projection-open.txt` with its reason. None is proved, none is refuted; failure to prove is not
evidence of falsity. The two `Complexity.FP` obligations of the certificate are in `Certificate.lean`.

* `prescribe_prefix_exists` — T3.3, the honest positive form of dose-response Lemma 4.3: for every
  computable `[0,1]` prefix table there is *some* inductor carrying it. The LIA construction started
  from an arbitrary finite history; the obstruction anson-051 names is that traders' trade sizes on
  the prefix days are not a priori bounded, so the budgeter must absorb finite prefix losses.
* T6.2 (`limit_non_recoverable`) **moved to `Church.lean` in repair round 1 and proved outright in
  repair round 2** (the Σ₁ route `rePred_comp_numeralSubst` replaced the coding fact
  `numeralSubst_code_computable`, which stays in `Church.lean` as an OPEN of record that nothing
  rests on).
* `conditioned_record_not_injective`, `conditioned_limitRecord_not_injective` — **T6.1, the
  source's precise target** (added in repair round 2, audit r2 fidelity B1): anson-2-018 asks for
  two inductors over the same process with *identical conditioned records on the whole language*
  (the evaluative sentence included) and a different unconditional limit, by a modification "only
  on `¬Q_A`-worlds". The package's `u1_u2_inductor` proves the `u`-free-record version only, which
  is *weaker* (the record there is blind to the sentence whose limit differs). Two readings are
  stated: agreement of the conditioned records **at every stage** (the source's words) and
  agreement of their **limits** (the reading every mixture construction can reach). Neither is
  proved nor refuted. What a proof needs: a *conditional projection* — a projection of the fresh
  atom with weight `c` on `ψ`-worlds and `c'` on `∼ψ`-worlds (`χ ↦ c·H(χ[⊤] ⋏ ψ) + (1−c)·H(χ[⊥] ⋏ ψ)
  + c'·H(χ[⊤] ⋏ ∼ψ) + (1−c')·H(χ[⊥] ⋏ ∼ψ)`), whose inductor-hood is a world-dependent-weight
  version of Lemma A's transfer `combo_exploits_of_exploits` (the weight `λ(v) ∈ {c, c'}` is bounded
  away from `0` and `1`, which is all that argument uses) plus a certificate of the (A) kind; two
  such projections with the same `c` and different `c'` have the same limiting conditionals given
  `ψ` at *every* sentence and different limits on the atom and on `ψ`. At finite stages they differ
  on `φ ⋏ ψ` by `(c' − c'')·(H_n(φ[⊤] ⋏ ψ ⋏ ∼ψ) − H_n(φ[⊥] ⋏ ψ ⋏ ∼ψ))` — for the *raw* ratio; FAF's
  `conditionalQuote` is capped (`1` when `V ψ = 0` or `V (φ ⋏ ψ) ≥ V ψ`), so the two capped records
  can also coincide at a stage where both are capped (audit r3 fidelity N2) — which vanishes only in
  the limit — so the every-stage reading is not reached by this construction, and may be over-strong
  (findings F14). The plain projection does not help: its conditioned record *at* the atom differs
  from `H`'s on every day (audit r2 probe `RecordAtAtom.lean`), and only a conditioning sentence that
  decides the atom (`ψ := ∼u`, degenerate) hides that. Both OPENs take a **stage-indexed** family
  `ψ : ℕ → Sentence` since repair round 3 (the source's `Q_A^{(t)}`; audit r3 fidelity N1), the
  constant family being the special case the round-3 adversarial probe `OpenHypsInhabited.lean`
  inhabits (`ψ := fun _ => projAtom 1` in the family form).
* `multiplicity_entangled` — T7.1 (anson-037, "the crux"): two inductors over `paperDP T` with
  different limits on the decomposition of an independent sentence. The projection does not apply
  (`paperPrimeDecompose σ` is not an atom fresh for the process); the "stronger process" route of
  settlement-target §6 changes the process.
* `exact_marginal_exists` — T7.3 (anson-2-003, "for every `t`"): an inductor with `P n (atom u) = c`
  *exactly* at every day. The projection gives the limit form only (zip AUDIT §2.6). Attempt angle:
  normalise `project` at `u`, `∼u` to `c`, `1 − c`; the discrepancy `c(1 − P n ⊤) − (1 − c) P n ⊥` is
  summable (T4.4) but `EF` coefficients re-evaluate at the changed prices, so
  `Exploits.of_boundedDifference` does not apply directly.
* `finiteVariation_projection` — T7.5 (dose-response open problem 2): Lemma A for a weight of finite
  total variation; the obstruction is the exposure-times-variation bound on `Σ (q m − λ) D m`.
* `twoAtom_projection_exists` — T1.8(b) at two atoms: a fully supported measure on the four cells
  realised as limits; the single-atom proof's `2`-way split becomes `4`-way.
* `convergence_rate_not_computable` — the extension, LI Proposition 5.5.1 (uncomputable convergence
  rates) — **moved to `Church.lean` and proved outright in repair round 3**: the market-side search
  it waited for is FAF's `paperPrimeDecomposeCode_prim` (`rateSearch_re`), and the rest is T6.2's
  engine.

Recorded, not stated in Lean (findings): T7.2 the measure-valued inductor (dropped substrate), T7.6
Theorem 2 bin form, T7.7 usefulness forces an uninspectable channel, T7.8 recursive inseparability,
and the eigenprior/Knaster–Tarski diagnosis (not an FAF object).
-/

namespace Cleanroom.Li.LiProjection

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Filter Topology
open LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

/-- **OPEN (T3.3).** For every computable process, day `N`, and computable `[0,1]` table on days
`< N`, there is a logical inductor with exactly that prefix.
Source: [[dose-response]] §4 Lemma 4.3 (statement); [[anson-inventory]] 051
Kind: OPEN
Fidelity: exact (the existence reading)
Hyps: n/a -/
theorem prescribe_prefix_exists (DP : DeductiveProcess) (hDP : ComputableDeductiveProcess DP)
    (N : ℕ) (t : ℕ → Sentence → ℚ) (ht : Computable fun p : ℕ × Sentence => t p.1 p.2)
    (ht01 : ∀ n φ, 0 ≤ t n φ ∧ t n φ ≤ 1) :
    ∃ P : History, IsLogicalInductor P DP ∧ ∀ n < N, ∀ φ, P n φ = (t n φ : ℝ) := by
  sorry

/-- **OPEN (T6.1, the source's precise target — every-stage reading).** For an inductor `H` over
`DP`, a fresh atom `u` (room for the modification), and a `u`-free **stage-indexed** conditioning
family `ψ : ℕ → Sentence` (the source's quote profile `Q_A^{(t)}`, the mandate's T6.1 and
`u1_u2_inductor`'s `ψ`; a constant family is the special case — generalised in repair round 3,
audit r3 fidelity N1) such that at every stage `n` both a `ψ n`-world and a `∼ψ n`-world are
stage-consistent (so `H_∞`-mass on the "`¬Q_A`-worlds" the source modifies on is positive, and the
conditioned record is not `conditionalQuote`'s junk default *in the limit* — FAF's quote is capped,
`1` when the denominator is `0` or the numerator reaches it, so at a finite stage with
`H n (ψ n) = 0` the record can still be the cap; audit r3 fidelity N2): a second inductor `H'` over
`DP` whose conditioned record on `ψ` agrees with `H`'s **at every sentence and every day** — the
evaluative sentence included, unlike `u1_u2_inductor` — and whose unconditional limit differs
somewhere. The source's U1/U2 as phrased ("identical `Q_A`-conditionals at every stage"). Neither
proved nor refuted; the mixture constructions reach only the limit reading
(`conditioned_limitRecord_not_injective`), see the module header and [[li-projection-findings]] F14.
Source: [[anson-2-inventory]] 018 (U1/U2; chat 05 L10265, L10802: "two base LIs `H, H'` over the same `D_H` with identical `Q_A`-conditionals at every stage but `H_∞(φ) ≠ H'_∞(φ)`"); audit r2 fidelity B1; audit r3 fidelity N1 (the family)
Kind: OPEN
Fidelity: exact (the source's every-stage phrasing over a stage-indexed family; a fresh atom supplied as the modification's carrier)
Hyps: n/a -/
theorem conditioned_record_not_injective (DP : DeductiveProcess) (u : ℕ) (hu : AtomFreeProcess u DP)
    (H : History) [IsLogicalInductor H DP] (ψ : ℕ → Sentence) (hψ : ∀ t, AtomFreeSentence u (ψ t))
    (hpos : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds (ψ n))
    (hneg : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ ¬ v.Holds (ψ n)) :
    ∃ H' : History, IsLogicalInductor H' DP ∧
      (∀ n φ, conditionedHistory H' ψ n φ = conditionedHistory H ψ n φ) ∧
      ∃ φ, limitingBelief H' φ ≠ limitingBelief H φ := by
  sorry

/-- **OPEN (T6.1, the source's precise target — limit reading).** As `conditioned_record_not_injective`
(same stage-indexed family `ψ`, same hypotheses), with the conditioned records required to agree
only in the limit (`limitingBelief` of the conditioned history, at every sentence): the reading a
conditional projection reaches (module header). Still a different unconditional limit somewhere (on
the atom, and on `ψ` itself, for that construction). Neither proved nor refuted.
Source: [[anson-2-inventory]] 018 (U1/U2, chat 05 L10802: "`H_∞(φ) = H_t(φ | Q_A)H_t(Q_A) + H_t(φ | ¬Q_A)H_t(¬Q_A)` depends on `H_t(Q_A)` … and `H_t(φ | ¬Q_A)`, neither observable"); audit r2 fidelity B1; audit r3 fidelity N1 (the family)
Kind: OPEN
Fidelity: variant: agreement of the records in the limit rather than at every stage
Hyps: n/a -/
theorem conditioned_limitRecord_not_injective (DP : DeductiveProcess) (u : ℕ)
    (hu : AtomFreeProcess u DP) (H : History) [IsLogicalInductor H DP] (ψ : ℕ → Sentence)
    (hψ : ∀ t, AtomFreeSentence u (ψ t))
    (hpos : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds (ψ n))
    (hneg : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ ¬ v.Holds (ψ n)) :
    ∃ H' : History, IsLogicalInductor H' DP ∧
      (∀ φ, limitingBelief (conditionedHistory H' ψ) φ =
        limitingBelief (conditionedHistory H ψ) φ) ∧
      ∃ φ, limitingBelief H' φ ≠ limitingBelief H φ := by
  sorry

/-- **OPEN (T7.1).** Multiplicity for an entangled sentence: for `σ` independent of `T`, two inductors
over `paperDP T` with different limiting beliefs on `paperPrimeDecompose σ`.
Source: [[anson-inventory]] 037 (chat 09 L343, "the crux"); [[self-referential-settlement-target]] §6
Kind: OPEN
Fidelity: exact
Hyps: n/a -/
theorem multiplicity_entangled (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Consistent T]
    (σ : ArithmeticSentence) (h1 : T ⊬ σ) (h2 : T ⊬ ∼σ) :
    ∃ P P' : History, IsLogicalInductor P (paperDP T) ∧ IsLogicalInductor P' (paperDP T) ∧
      limitingBelief P (paperPrimeDecompose σ) ≠ limitingBelief P' (paperPrimeDecompose σ) := by
  sorry

/-- **OPEN (T7.3).** Exact per-stage constrained existence: an inductor over `DP` whose price of the
fresh atom `u` is *exactly* `c` on every day.
Source: [[anson-2-inventory]] 003 ("for every `t`"); zip AUDIT §2.6 (the exact marginal is not available from the projection)
Kind: OPEN
Fidelity: exact
Hyps: n/a -/
theorem exact_marginal_exists (DP : DeductiveProcess) (hDP : ComputableDeductiveProcess DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u : ℕ) (hu : AtomFreeProcess u DP)
    (c : ℚ) (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ P : History, IsLogicalInductor P DP ∧ ∀ n, P n (Formula.atom u) = (c : ℝ) := by
  sorry

/-- **OPEN (T7.5).** Lemma A for a weight of finite total variation (`Σ |q (n+1) − q n| < ∞`) in
place of eventual constancy.
Source: [[dose-response]] §8 open problem 2; [[anson-inventory]] 044 (general varying marginals)
Kind: OPEN
Fidelity: exact
Hyps: n/a -/
theorem finiteVariation_projection (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (u : ℕ) (hu : AtomFreeProcess u DP) (q : ℕ → ℚ) (η : ℚ) (hη : 0 < η)
    (hq : ∀ n, η ≤ q n ∧ q n ≤ 1 - η) (hqec : MachineRatCodes q)
    (hvar : Summable fun n => |(q (n + 1) : ℝ) - q n|) :
    IsLogicalInductor (project P u q) DP := by
  sorry

/-- **OPEN (T1.8(b)).** Two fresh atoms with a fully supported measure on the four cells: an inductor
over `DP` whose limiting beliefs on the four conjunctions are the cell masses.
Source: chat 09 L5773–5811 (the multi-atom form, fully supported `μ`)
Kind: OPEN
Fidelity: variant: two atoms
Hyps: n/a -/
theorem twoAtom_projection_exists (DP : DeductiveProcess) (hDP : ComputableDeductiveProcess DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u₁ u₂ : ℕ) (hne : u₁ ≠ u₂)
    (hu₁ : AtomFreeProcess u₁ DP) (hu₂ : AtomFreeProcess u₂ DP) (μ : Bool → Bool → ℚ)
    (hpos : ∀ b₁ b₂, 0 < μ b₁ b₂)
    (hsum : μ true true + μ true false + μ false true + μ false false = 1) :
    ∃ P : History, IsLogicalInductor P DP ∧
      limitingBelief P (Formula.atom u₁ ⋏ Formula.atom u₂) = μ true true ∧
      limitingBelief P (Formula.atom u₁ ⋏ ∼Formula.atom u₂) = μ true false ∧
      limitingBelief P (∼Formula.atom u₁ ⋏ Formula.atom u₂) = μ false true ∧
      limitingBelief P (∼Formula.atom u₁ ⋏ ∼Formula.atom u₂) = μ false false := by
  sorry

end Cleanroom.Li.LiProjection
