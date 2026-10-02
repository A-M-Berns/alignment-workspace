import Cleanroom.Deference.DefSelfTrust.Est
import Cleanroom.Deference.DefSelfTrust.RobustSelfTrust
import Cleanroom.Deference.DefSelfTrust.Legitimacy
import LogicalInduction.Framework.Machine.Witnesses

/-!
# `def-self-trust` — the witness of `est`: a source whose gate is provably live and dead infinitely often (N−)

`def-lattice`'s `weightQuoteWitness` inhabits `est`'s hypothesis package with a non-constant
source (the atom family) but says nothing about the gate `Ind_δ(E_{f(n)}(X_n) > s)`: nothing is
known about the paper inductor's prices on undecided atoms, so the gate could, for all the
witness shows, be eventually `0` (a degenerate instance in which `est` reads `0 ≳ₙ 0`). The
mandate asks for a witness whose deferred expectation *crosses the threshold with the gate live
infinitely often*.

The **parity family** does it provably: `φ_n := ∼(a_n ⋏ ∼a_n)` (a theorem) on even days and
`a_n ⋏ ∼a_n` (refutable) on odd days. The self-expert's estimate of `literalIndicator (φ_n)` is
the deferred price `P_{f(n)}(φ_n)`; by `thm:provind` on the reindexed families
`m ↦ φ_{f⁻¹ m}` it tends to `1` along even `n` and to `0` along odd `n`, so at `s = 1/2`,
`δ = 1/4` the gate is `1` on all large even days and `0` on all large odd days
(`estWitness_gate_live`, `estWitness_gate_dead`). The source is non-constant
(`parityFamily_nonconstant`), the ramp `WeightQuote` is FAF's own `thm:st` package projected by
`WeightQuote.of_selfTrustQuote` (`slack ≡ 0`), and `est` on it is `estWitness_est`.

**Grade: N− for the content of `est`** (repair round 1, after the round-1 adversarial audit B3
and fidelity audit N1). The parity source is *decided*: every completed-theory world pays `1`
on even days and `0` on odd days, so on this witness the bet `XW − ½·W` is world-nonnegative
(`½·gate` on even days, `−½·gate = 0` eventually on odd days) and the conclusion of `est`
follows from `thm:provind` plus one eventual `thm:expprovind` **without `ccee`** — the audit's
probe `audit-r1-probes/EstWitnessDecided.lean` re-derives `estWitness_est`'s statement that
way. The witness therefore inhabits the package non-vacuously (non-constant source, real
construction, gate provably live and dead i.o. — the mandate's stated bar) but does not
exercise the self-trust step (the present expectation respecting a gate keyed to the *future*
price). This is structural over `paperDP T`: a gate that is provably live i.o. needs the
deferred price provably far from the threshold, which (absent `li-pseudorandom` T7) means a
source decided in every completed theory of `T` — and a decided source's world value and gate
are decided together. A content-exercising witness needs a source whose completed-theory value
and deferred price decouple with the gate provably live: a pseudorandom family at frequency
`p > s + δ` (payout `0` on a `p`-fraction of days in every world while the gate is live), i.e.
`li-pseudorandom`'s family over `atomDP`, on which `est` is not stated (`est` is over
`paperDP T`; the `unionStar (paperDP T)` shape would host it, over T7). `def-lattice`'s
`weightQuoteWitness` (undecided atoms) has the decoupling but no provable gate crossing. So the
two half-witnesses together cover non-vacuity (this file) and decoupling (`def-lattice`), and
the content-exercising witness is out of reach without T7 or an `est` over `unionStar`.

**Theorem B's inhabitants (repair round 2).** The same structural limit applies to Theorem B,
and both round-2 audits (fidelity B1, adversarial B1) showed that the inhabitant shipped in
repair round 1, `theoremB_parity_instance` at Prop 6.3's data (`c ≡ 1/2`, `t = 2/5`,
`δ = 1/20`), is worse than N− for the content: Theorem B's conclusion is *vacuous* on it. The
deferred price `Y_n` tends to `1`/`0`, so the residual `min(1, 20·|1/2 − Y_n|)` is `1`
eventually in every world, `E_n(⌜e_n⌝) → 1`, and the right-hand side `(2/5)·E_n(⌜û_n⌝) −
(7/5)·E_n(⌜e_n⌝)` tends to at most `−1` while the left-hand side is an expectation in `[0,1]`
(the audits' probes `audit-r2-probes/TheoremBParityVacuous.lean` and
`TheoremBInstanceVacuous.lean` re-derive its exact statement without Theorem B). That is
Prop 6.3's own `e ≡ 1` regime, and the instance is kept — regraded N− — as the realisation of
that regime over the paper inductor. The **parity-tracking forecast** `c_n := 1` on even days,
`0` on odd days (`parityForecast`, computable) is the inhabitant on which the bound *bites*: it
satisfies `(UA)` on the parity source (`parityForecast_UA`, since `Y_n → 1`/`0` along the two
parities), so the residual's expectation vanishes (`parityForecast_residual_vanishes`),
Corollary B.1 applies (`parityForecast_corollaryB1`), and the right-hand side of Theorem B
exceeds `1/5` infinitely often (`theoremB_parityForecast_bound_bites`: the gate expectation
exceeds `3/4` on all large even days). It is still N− for the content: on *any* decided
source Theorem B is `provind`-implied for every forecast (with payout `1` the bound reads
`û_n ≥ t·û_n`; with payout `0` it reads `t·û_n ≤ (1+t)·e_n`, which the ramp arithmetic gives
once `Y_n → 0`), so a content-exercising inhabitant needs an undecided source with a provable
gate crossing — the pseudorandom family over T7, as for `est`. The two inhabitants together
show the package is inhabited (round 1) and the conclusion is non-vacuous on it (round 2); no
instance over `paperDP T` exercises Lemma C's transfer or `est`'s self-trust step.

**A non-constant generable gate for the gated `est`** (repair round 2, after the round-2
adversarial audit N7): `gatedSelfTrust_parity_instance` instantiates
`gatedSelfTrust_productForm` on the parity source at `w := estWeight … (1/4) (1/2)` — the ramp
of the deferred price itself, a P-generable `[0,1]` gate that is not constant: the product
gate `Ind_δ(E_{f n}(X_n) > s) · w_{f n}` is the square of the witness gate, `1` on all large
even days (`gatedParity_gate_live`) and `0` on all large odd days. N− for the same reason as
`estWitness_est`.
-/

namespace Cleanroom.Deference.DefSelfTrust

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice
open Cleanroom.Found.LiAsympCalc
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional

noncomputable section

/-! ## The parity family -/

/-- The refutable member `a_n ⋏ ∼a_n`.
Source: none: infrastructure (witness)
Kind: D
Fidelity: n/a -/
def contraAtom (n : ℕ) : Sentence := (Formula.atom n : Sentence) ⋏ ∼(Formula.atom n : Sentence)

/-- The theorem member `∼(a_n ⋏ ∼a_n)`.
Source: none: infrastructure (witness)
Kind: D
Fidelity: n/a -/
def tautAtom (n : ℕ) : Sentence := ∼(contraAtom n)

/-- The parity family: a theorem on even days, a refutable sentence on odd days.
Source: mandate target 2 ("the source must be non-constant and its deferred expectation must
cross the threshold with the gate live infinitely often")
Kind: D
Fidelity: n/a -/
def parityFamily (n : ℕ) : Sentence := if n % 2 = 0 then tautAtom n else contraAtom n

/-- Every world refutes `contraAtom n`.
Source: none: infrastructure (propositional)
Kind: L
Fidelity: n/a -/
theorem holds_neg_contraAtom (v : PCWorld) (n : ℕ) : v.Holds (∼(contraAtom n)) := by
  rw [PCWorld.holds_neg, contraAtom, PCWorld.holds_and, PCWorld.holds_neg]
  tauto

/-- The refutable members are machine-metered.
Source: FAF `machineSentenceCodes_atom`, `MachineSentenceCodes.and`, `.neg`
Kind: L
Fidelity: n/a -/
theorem contraAtom_codes : MachineSentenceCodes contraAtom :=
  machineSentenceCodes_atom.and machineSentenceCodes_atom.neg

/-- The theorem members are machine-metered.
Source: FAF `MachineSentenceCodes.neg`
Kind: L
Fidelity: n/a -/
theorem tautAtom_codes : MachineSentenceCodes tautAtom := contraAtom_codes.neg

/-- The parity family is machine-metered (FAF's `modDispatch` on the parity of the day).
Source: FAF `MachineSentenceCodes.modDispatch`
Kind: L
Fidelity: n/a -/
theorem parityFamily_codes : MachineSentenceCodes parityFamily := by
  have h := MachineSentenceCodes.modDispatch (k := 2) (by norm_num)
    (φ := fun j n => if j = 0 then tautAtom n else contraAtom n)
    (fun j _ => by
      by_cases hj : j = 0
      · subst hj; simpa using tautAtom_codes
      · simpa [hj] using contraAtom_codes)
  refine (h.comp (UnaryRuler.id.pair UnaryRuler.id)).of_eq (fun n => ?_)
  simp only [Nat.unpair_pair]
  rfl


/-- The parity family is not a constant sequence — infinitely often so: consecutive members
`φ_{2n}` (a theorem) and `φ_{2n+1}` (refutable) are distinguished by any world (semantically, not
by syntax).
Source: mandate target 2 (N+: not a constant sequence)
Kind: N+
Fidelity: n/a -/
theorem parityFamily_nonconstant (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] (n : ℕ) : parityFamily (2 * n) ≠ parityFamily (2 * n + 1) := by
  intro h
  obtain ⟨v, -⟩ := paperDP_hworld T 0
  have h1 : v.Holds (parityFamily (2 * n)) := by
    unfold parityFamily
    rw [if_pos (by omega)]
    exact holds_neg_contraAtom v _
  have h2 : ¬ v.Holds (parityFamily (2 * n + 1)) := by
    unfold parityFamily
    rw [if_neg (by omega)]
    exact (PCWorld.holds_neg v _).1 (holds_neg_contraAtom v _)
  exact h2 (h ▸ h1)

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- The gate of the witness at `(s, δ) = (1/2, 1/4)`: the ramp of the deferred price.
Source: none: infrastructure (witness)
Kind: D
Fidelity: n/a -/
def witnessGate (f : DeferralFunction) (n : ℕ) : ℝ :=
  ctsInd (1 / 4 : ℚ) (liaHistory (paperDP T) (f n) (parityFamily n)) ((1 / 2 : ℚ) : ℝ)

/-- Along the deferral, the price of the reindexed theorem family tends to `1`
(`thm:provind`), hence the deferred price of `tautAtom n` exceeds `3/4` eventually.
Source: FAF `lic_provind_true`
Kind: L
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem deferred_price_taut_eventually (f : DeferralFunction) (hinj : Function.Injective f.f) :
    ∀ᶠ n in atTop, (3 / 4 : ℝ) < liaHistory (paperDP T) (f n) (tautAtom n) := by
  have h := lic_provind_true (liaHistory (paperDP T)) (paperDP T)
    (fun m => tautAtom (deferralPreimage f m)) (tautAtom_codes.comp (unaryRuler_deferralPreimage f))
    (fun m v _ => holds_neg_contraAtom v _) (paperDP_hworld T)
  have h' : Tendsto (fun m => liaHistory (paperDP T) m (tautAtom (deferralPreimage f m)) - 1)
      atTop (𝓝 0) := h
  have hev : ∀ᶠ m in atTop,
      (3 / 4 : ℝ) < liaHistory (paperDP T) m (tautAtom (deferralPreimage f m)) := by
    filter_upwards [h'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
      h'.eventually (lt_mem_nhds (by norm_num : (-(1 / 4) : ℝ) < 0))] with m h1 h2
    linarith
  have hf : Tendsto f.f atTop atTop := f.tendsto_atTop
  filter_upwards [hf.eventually hev] with n hn
  rwa [deferralPreimage_at f hinj] at hn

/-- Along the deferral, the price of the reindexed refutable family tends to `0`
(`thm:provind`), hence the deferred price of `contraAtom n` is below `1/2` eventually.
Source: FAF `lic_provind_false`
Kind: L
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem deferred_price_contra_eventually (f : DeferralFunction) (hinj : Function.Injective f.f) :
    ∀ᶠ n in atTop, liaHistory (paperDP T) (f n) (contraAtom n) < (1 / 2 : ℝ) := by
  have h := lic_provind_false (liaHistory (paperDP T)) (paperDP T)
    (fun m => contraAtom (deferralPreimage f m))
    (contraAtom_codes.comp (unaryRuler_deferralPreimage f))
    (fun m v _ => holds_neg_contraAtom v _) (paperDP_hworld T)
  have h' : Tendsto (fun m => liaHistory (paperDP T) m (contraAtom (deferralPreimage f m)) - 0)
      atTop (𝓝 0) := h
  have hev : ∀ᶠ m in atTop,
      liaHistory (paperDP T) m (contraAtom (deferralPreimage f m)) < (1 / 2 : ℝ) := by
    filter_upwards [h'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with m h1
    linarith
  have hf : Tendsto f.f atTop atTop := f.tendsto_atTop
  filter_upwards [hf.eventually hev] with n hn
  rwa [deferralPreimage_at f hinj] at hn

/-- Even days are frequent.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem frequently_even' : ∃ᶠ n : ℕ in atTop, n % 2 = 0 :=
  Filter.frequently_atTop.2 (fun N => ⟨2 * N, by omega, by omega⟩)

/-- Odd days are frequent.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem frequently_odd' : ∃ᶠ n : ℕ in atTop, n % 2 ≠ 0 :=
  Filter.frequently_atTop.2 (fun N => ⟨2 * N + 1, by omega, by omega⟩)

/-- **The gate is live infinitely often**: `Ind_{1/4}(P_{f(n)}(φ_n) > 1/2) = 1` on all large even
days (`thm:provind` on the reindexed theorem family).
Source: mandate target 2 ("a lemma that the witness gate is not eventually `0`")
Kind: L
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem estWitness_gate_live (f : DeferralFunction) (hinj : Function.Injective f.f) :
    ∃ᶠ n in atTop, witnessGate T f n = 1 := by
  refine (frequently_even'.and_eventually (deferred_price_taut_eventually T f hinj)).mono ?_
  rintro n ⟨hn, hp⟩
  unfold witnessGate parityFamily
  rw [if_pos hn, ctsInd_eq_one_iff (by norm_num)]
  push_cast
  linarith

/-- **The gate is dead infinitely often**: the ramp is `0` on all large odd days
(`thm:provind` on the reindexed refutable family).
Source: mandate target 2 (the gate crosses the threshold)
Kind: L
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem estWitness_gate_dead (f : DeferralFunction) (hinj : Function.Injective f.f) :
    ∃ᶠ n in atTop, witnessGate T f n = 0 := by
  refine (frequently_odd'.and_eventually (deferred_price_contra_eventually T f hinj)).mono ?_
  rintro n ⟨hn, hp⟩
  unfold witnessGate parityFamily
  rw [if_neg hn, ctsInd_eq_zero_iff (by norm_num)]
  push_cast
  linarith

/-! ## FAF's `thm:st` package on the parity family, projected to a ramp `WeightQuote` -/

/-- FAF's confidence quote code of the paper market at the deferred day for the parity family,
`(δ, s) = (1/4, 1/2)`.
Source: FAF `paperConfidenceQuoteCode`; the pattern of `def-lattice` `Witness.confidenceCode`
Kind: D
Fidelity: n/a -/
def parityConfidenceCode (f : DeferralFunction) :=
  paperConfidenceQuoteCode T f parityFamily parityFamily_codes (fun _ => (1 / 4 : ℚ))
    (fun _ => (1 / 2 : ℚ)) (MachineRatCodes.const (1 / 4)).computable
    (PGenerableRat.ofMachineRatCodes (MachineRatCodes.const (1 / 2)) _)

/-- The witness's weight LUV `W n = ⌜Ind_{1/4}(P_{f(n)}(φ_n) > 1/2)⌝`.
Source: FAF `RationalQuoteCode.luv`
Kind: D
Fidelity: n/a -/
def parityW (f : DeferralFunction) (n : ℕ) : LUV := (parityConfidenceCode T f).luv n

/-- The witness's product LUV `XW n = ⌜1(φ_n) · Ind_{1/4}(…)⌝` (exact indicator product).
Source: FAF `indicatorProductLUV`
Kind: D
Fidelity: n/a -/
def parityXW (f : DeferralFunction) (n : ℕ) : LUV :=
  indicatorProductLUV (parityConfidenceCode T f) parityFamily n

omit [Entailment.Consistent T] in
/-- The confidence quote reflects the ramp of the deferred price.
Source: FAF `RationalQuoteCode.reflected`, `paperConfidence_value_cast`
Kind: L
Fidelity: n/a -/
lemma parityW_reflected (f : DeferralFunction) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt (parityW T f n)
      (ctsInd ((fun _ => (1 / 4 : ℚ)) n) (liaHistory (paperDP T) (f n) (parityFamily n))
        (((fun _ => (1 / 2 : ℚ)) n : ℚ) : ℝ)) := by
  have h := RationalQuoteCode.reflected (paperQuotationPresentation T) (parityConfidenceCode T f)
    n v hv
  rwa [← paperConfidence_value_cast T f parityFamily (fun _ => (1 / 4 : ℚ)) (fun _ => (1 / 2 : ℚ)) n]
    at h

omit [Entailment.Consistent T] in
/-- The product quote reflects `payout(φ_n) · ramp`.
Source: FAF `indicatorProductLUV_valuesAt`, `paperConfidence_value_cast`
Kind: L
Fidelity: n/a -/
lemma parityXW_reflected (f : DeferralFunction) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt (parityXW T f n)
      (v.payout (parityFamily n) *
        ctsInd ((fun _ => (1 / 4 : ℚ)) n) (liaHistory (paperDP T) (f n) (parityFamily n))
          (((fun _ => (1 / 2 : ℚ)) n : ℚ) : ℝ)) := by
  have h := indicatorProductLUV_valuesAt (paperQuotationPresentation T) (parityConfidenceCode T f)
    parityFamily n v hv
  rwa [← paperConfidence_value_cast T f parityFamily (fun _ => (1 / 4 : ℚ)) (fun _ => (1 / 2 : ℚ)) n]
    at h

/-- FAF's complete `thm:st` package on the parity family at `(δ, s) = (1/4, 1/2)`.
Source: FAF `selfTrustQuoteOfRepresentation`; the pattern of `def-lattice`
`Witness.selfTrustQuoteWitness`
Kind: D
Fidelity: n/a -/
def paritySelfTrustQuote (f : DeferralFunction) :
    SelfTrustQuote (liaHistory (paperDP T)) (paperDP T) f parityFamily (fun _ => (1 / 4 : ℚ))
      (fun _ => (1 / 2 : ℚ)) (parityXW T f) (parityW T f) :=
  selfTrustQuoteOfRepresentation f parityFamily (fun _ => (1 / 4 : ℚ)) (fun _ => (1 / 2 : ℚ))
    (parityXW T f) (parityW T f) (fun _ => by norm_num) (fun _ => by norm_num)
    parityFamily_codes (MachineRatCodes.const (1 / (1 / 4 : ℚ)))
    (PGenerableRat.ofMachineRatCodes (MachineRatCodes.const (1 / 2)) _).choose
    (PGenerableRat.ofMachineRatCodes (MachineRatCodes.const (1 / 2)) _).choose_spec
    (indicatorProductLUV_machineThresholdCodeSeq _ parityFamily_codes)
    (parityConfidenceCode T f).poly
    (parityW_reflected T f) (parityXW_reflected T f)
    (paperDP_hworld T)

/-- **The witness of `est`'s hypothesis package** (mandate target 2): the ramp `WeightQuote`
for the self-expert on the parity source at `(s, δ) = (1/2, 1/4)`, `slack ≡ 0`, whose gate is
provably live infinitely often (`estWitness_gate_live`) and dead infinitely often
(`estWitness_gate_dead`); the source is not constant (`parityFamily_nonconstant`). **Grade N−
for the content**: the source is decided in every completed-theory world, so on it `est`
follows from `thm:provind` alone and the `ccee` step is idle (module docstring; round-1
adversarial audit B3, probe `EstWitnessDecided.lean`). It meets the mandate's stated N+ bar
(non-constant source, gate live and dead i.o., the real inductor) and establishes non-vacuity
of the package; the content-exercising witness (decoupled source with a provable gate
crossing) is out of reach over `paperDP T` without `li-pseudorandom` T7.
Source: mandate target 2 (witness); `def-lattice` `WeightQuote.of_selfTrustQuote`
Kind: N−
Fidelity: n/a -/
def estWitnessQuote (f : DeferralFunction) :
    WeightQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
      (fun n => literalIndicator (parityFamily n)) (rampAbove (1 / 4) (1 / 2))
      (parityW T f) (parityXW T f) :=
  WeightQuote.of_selfTrustQuote (paritySelfTrustQuote T f)

/-- **`est` on the witness** (above face): `E_n(XW_n) − (1/2)·E_n(W_n) ≳ₙ 0` over the paper's
inductor for the parity source — the headline `selfSoftTotalTrustAbove` at the witness package.
The gate takes both values infinitely often, so the instance is not `0 ≳ₙ 0`; but the source is
decided, so this conclusion also follows from `thm:provind` without `est` (grade N− for the
content, module docstring). The below face at the same source (down-ramp `1` on large odd
days, `0` on large even days) is not written: FAF's `thm:st` package and
`WeightQuote.of_selfTrustQuote` give the above ramp only.
Source: mandate target 2 (witness)
Kind: N−
Fidelity: exact (indicator source, `slack ≡ 0`)
Hyps: (a); `hinj` -/
theorem estWitness_est (f : DeferralFunction) (hinj : Function.Injective f.f) :
    (fun n => (parityXW T f n).expect (liaHistory (paperDP T)) n -
      ((1 / 2 : ℚ) : ℝ) * (parityW T f n).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun _ => (0 : ℝ)) :=
  selfSoftTotalTrustAbove T f hinj (1 / 2) (by norm_num : (0 : ℚ) < 1 / 4) _ _ _
    (literalIndicator_machineThresholdCodeSeq parityFamily_codes) (estWitnessQuote T f)

/-- The witness over `𝗣𝗔` at `succDeferral`: gate live and dead infinitely often (the instance
binders discharged; an instantiability check).
Source: mandate target 2 (witness); mandate design decision 1
Kind: L
Fidelity: n/a -/
example : (∃ᶠ n in atTop, witnessGate 𝗣𝗔 succDeferral n = 1) ∧
    (∃ᶠ n in atTop, witnessGate 𝗣𝗔 succDeferral n = 0) :=
  ⟨estWitness_gate_live 𝗣𝗔 succDeferral succDeferral_injective,
    estWitness_gate_dead 𝗣𝗔 succDeferral succDeferral_injective⟩

/-! ## The parity source as an inhabitant of Theorem B's hypothesis package -/

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The parity source is world-valued (a literal indicator is valued at the payout).
Source: round-1 adversarial audit N2 (probe `TheoremBInhabited.lean`); FAF
`literalIndicator_valuesAt`
Kind: L
Fidelity: n/a -/
theorem paritySource_valued :
    Valued (paperDP T) (fun n => literalIndicator (parityFamily n)) :=
  fun n _ hv => ⟨_, literalIndicator_valuesAt (parityFamily n) (paperDP T) hv⟩

/-- **Theorem B's hypothesis package is inhabited at Prop 6.3's data, where the bound is
vacuous** (round-1 adversarial audit N2, ported from its probe; **regraded N− in repair round
2** after the round-2 fidelity audit B1 and adversarial audit B1): `T := 𝗣𝗔`,
`f := succDeferral`, the parity source (e.c., world-valued, non-constant), the constant
forecast `c ≡ 1/2`, `t := 2/5`, `δ := 1/20`. On this instance the forecast is wrong in the
limit on every day — the deferred price `Y_n` of the parity family exceeds `3/4` on all large
even days and is below `1/2` on all large odd days (`deferred_price_taut_eventually`,
`deferred_price_contra_eventually`; by `thm:provind` it tends to `1`/`0`) — so the mandate's
`c = Y` trap is avoided, **but** for the same reason the residual `min(1, 20·|1/2 − Y_n|)` is
`1` eventually in every world, `E_n(⌜e_n⌝) → 1`, and the right-hand side
`(2/5)·E_n(⌜û_n⌝) − (7/5)·E_n(⌜e_n⌝)` tends to at most `−1` while the left-hand side is an
expectation in `[0,1]`: the conclusion holds for a reason that has nothing to do with Theorem
B (probes `audit-r2-probes/TheoremBParityVacuous.lean`, `TheoremBInstanceVacuous.lean`
re-derive this exact statement from `thm:provind` and `expect_mem_Icc`). This is Prop 6.3's
`e ≡ 1` regime realised over the paper inductor — the regime in which "Theorem B says
nothing" — kept as that realisation. The inhabitant on which the bound bites is
`theoremB_parityForecast_instance` (below). It is **not** an inductor-level Prop 6.3:
`E_n(X_n)` also tends to `1`/`0`, so the per-day target `û (E_n(X_n) − t) ≥ 0` fails on odd
days; Prop 6.3's inductor-level form needs a target on which the novice itself sits near `1/2`
(pseudorandom, over `li-pseudorandom` T7).
Source: vq-wiki-2-010 (Prop 6.3's data); mandate target 6e; round-1 adversarial audit N2;
round-2 audits B1
Kind: N− (inhabits the package; Theorem B's conclusion is vacuous on it)
Fidelity: n/a -/
theorem theoremB_parity_instance :
    (fun n => (meshProductLUV (forecastGate 𝗣𝗔 (Computable.const (1 / 2 : ℚ)) (1 / 20) (2 / 5))
        (fun n => literalIndicator (parityFamily n)) n).expect (liaHistory (paperDP 𝗣𝗔)) n) ≳ₙ
      (fun n => ((2 / 5 : ℚ) : ℝ) *
          ((forecastGate 𝗣𝗔 (Computable.const (1 / 2 : ℚ)) (1 / 20) (2 / 5)).luv n).expect
            (liaHistory (paperDP 𝗣𝗔)) n -
        (1 + ((2 / 5 : ℚ) : ℝ)) *
          ((truncError 𝗣𝗔 succDeferral
            (literalIndicator_machineThresholdCodeSeq parityFamily_codes)
            (Computable.const (1 / 2 : ℚ)) (by norm_num : (0 : ℚ) < 1 / 20)).luv n).expect
              (liaHistory (paperDP 𝗣𝗔)) n) :=
  theoremB 𝗣𝗔 succDeferral succDeferral_injective
    (literalIndicator_machineThresholdCodeSeq parityFamily_codes) (paritySource_valued 𝗣𝗔)
    (Computable.const (1 / 2 : ℚ)) (by norm_num : (0 : ℚ) < 1 / 20) (by norm_num : (0 : ℚ) ≤ 2 / 5)

/-! ## The parity-tracking forecast: the inhabitant of Theorem B's package on which the bound bites -/

/-- Along the deferral the price of the theorem member tends to `1` (`thm:provind` on the
reindexed family `m ↦ tautAtom (f⁻¹ m)`, read back along `f`).
Source: FAF `lic_provind_true`
Kind: L
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem deferred_price_taut_tendsto (f : DeferralFunction) (hinj : Function.Injective f.f) :
    Tendsto (fun n => liaHistory (paperDP T) (f n) (tautAtom n)) atTop (𝓝 1) := by
  have h := lic_provind_true (liaHistory (paperDP T)) (paperDP T)
    (fun m => tautAtom (deferralPreimage f m)) (tautAtom_codes.comp (unaryRuler_deferralPreimage f))
    (fun m v _ => holds_neg_contraAtom v _) (paperDP_hworld T)
  have h' : Tendsto (fun m => liaHistory (paperDP T) m (tautAtom (deferralPreimage f m)) - 1)
      atTop (𝓝 0) := h
  have h2 := (tendsto_sub_nhds_zero_iff.1 h').comp f.tendsto_atTop
  refine h2.congr (fun n => ?_)
  simp only [Function.comp, deferralPreimage_at f hinj]

/-- Along the deferral the price of the refutable member tends to `0` (`thm:provind` on the
reindexed family `m ↦ contraAtom (f⁻¹ m)`, read back along `f`).
Source: FAF `lic_provind_false`
Kind: L
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem deferred_price_contra_tendsto (f : DeferralFunction) (hinj : Function.Injective f.f) :
    Tendsto (fun n => liaHistory (paperDP T) (f n) (contraAtom n)) atTop (𝓝 0) := by
  have h := lic_provind_false (liaHistory (paperDP T)) (paperDP T)
    (fun m => contraAtom (deferralPreimage f m))
    (contraAtom_codes.comp (unaryRuler_deferralPreimage f))
    (fun m v _ => holds_neg_contraAtom v _) (paperDP_hworld T)
  have h' : Tendsto (fun m => liaHistory (paperDP T) m (contraAtom (deferralPreimage f m)) - 0)
      atTop (𝓝 0) := h
  have h2 := (tendsto_sub_nhds_zero_iff.1 h').comp f.tendsto_atTop
  refine h2.congr (fun n => ?_)
  simp only [Function.comp, deferralPreimage_at f hinj]

end

/-- The parity-tracking forecast: `1` on even days, `0` on odd days — the forecast that tracks
the parity source's settled value (and, in the limit, its deferred price).
Source: round-2 fidelity audit B1 / adversarial audit B1 (the "tracking forecast" both propose)
Kind: D
Fidelity: n/a -/
def parityForecast (n : ℕ) : ℚ := if n % 2 = 0 then 1 else 0

/-- The parity-tracking forecast is computable (Mathlib's `Primrec.ite` on the parity test).
Source: none: infrastructure (witness)
Kind: L
Fidelity: n/a -/
theorem parityForecast_computable : Computable parityForecast := by
  have h : Primrec (fun n : ℕ => if n % 2 = 0 then (1 : ℚ) else 0) :=
    Primrec.ite (PrimrecRel.comp Primrec.eq (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
      (Primrec.const 0)) (Primrec.const 1) (Primrec.const 0)
  exact h.to_comp

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- **The parity-tracking forecast satisfies `(UA)` on the parity source**: for every `ε > 0`,
eventually `|c_n − Y_n| < ε`, because the deferred price tends to `1` along even days and to
`0` along odd days (`thm:provind` on the two reindexed families). A non-trivial inhabitant of
Corollary B.1's scope condition (not the `c = Y` trap `deferredForecast_UA`): `c_n` is a fixed
computable sequence that never reads the market.
Source: vq-wiki-063 (`(UA)`); round-2 adversarial audit N1
Kind: L (`provind`-implied: the source is decided)
Fidelity: exact
Hyps: (a); `hinj` -/
theorem parityForecast_UA (f : DeferralFunction) (hinj : Function.Injective f.f) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
      |((parityForecast n : ℚ) : ℝ) -
        (literalIndicator (parityFamily n)).expect (liaHistory (paperDP T)) (f n)| < ε := by
  intro ε hε
  have h1 := deferred_price_taut_tendsto T f hinj
  have h0 := deferred_price_contra_tendsto T f hinj
  filter_upwards [h1.eventually (lt_mem_nhds (by linarith : (1 : ℝ) - ε < 1)),
    h1.eventually (gt_mem_nhds (by linarith : (1 : ℝ) < 1 + ε)),
    h0.eventually (lt_mem_nhds (by linarith : (-ε : ℝ) < 0)),
    h0.eventually (gt_mem_nhds hε)] with n ha hb hc hd
  rw [literalIndicator_expect]
  unfold parityForecast parityFamily
  split_ifs with h
  · push_cast
    rw [abs_sub_lt_iff]
    constructor <;> linarith
  · push_cast
    rw [abs_sub_lt_iff]
    constructor <;> linarith

/-- **Theorem B at the parity-tracking forecast** (`t = 2/5`, `δ = 1/20`): the inhabitant of
Theorem B's package on which the bound is non-vacuous — the residual's expectation vanishes
(`parityForecast_residual_vanishes`) and the right-hand side exceeds `1/5` infinitely often
(`theoremB_parityForecast_bound_bites`). **N− for the content**: the parity source is decided,
so Theorem B here is `provind`-implied for every forecast (module header); no instance over
`paperDP T` exercises Lemma C's transfer or `est`'s self-trust step.
Source: mandate target 6e; round-2 fidelity audit B1 / adversarial audit B1 (ii)
Kind: N− (inhabits the package; the bound is non-vacuous on it; the content is
`provind`-implied)
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem theoremB_parityForecast_instance (f : DeferralFunction)
    (hinj : Function.Injective f.f) :
    (fun n => (meshProductLUV (forecastGate T parityForecast_computable (1 / 20) (2 / 5))
        (fun n => literalIndicator (parityFamily n)) n).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun n => ((2 / 5 : ℚ) : ℝ) *
          ((forecastGate T parityForecast_computable (1 / 20) (2 / 5)).luv n).expect
            (liaHistory (paperDP T)) n -
        (1 + ((2 / 5 : ℚ) : ℝ)) *
          ((truncError T f (literalIndicator_machineThresholdCodeSeq parityFamily_codes)
            parityForecast_computable (by norm_num : (0 : ℚ) < 1 / 20)).luv n).expect
              (liaHistory (paperDP T)) n) :=
  theoremB T f hinj (literalIndicator_machineThresholdCodeSeq parityFamily_codes)
    (paritySource_valued T) parityForecast_computable (by norm_num : (0 : ℚ) < 1 / 20)
    (by norm_num : (0 : ℚ) ≤ 2 / 5)

/-- **The residual vanishes at the parity-tracking forecast**: `E_n(⌜min(1, 20·|c_n − Y_n|)⌝) ≈ₙ 0`
(Corollary B.1's first half at `parityForecast_UA`).
Source: vq-wiki-063 (Corollary B.1, "the residual vanishes"); round-2 audits B1 (ii)
Kind: C
Fidelity: exact
Hyps: (a); `hinj` -/
theorem parityForecast_residual_vanishes (f : DeferralFunction)
    (hinj : Function.Injective f.f) :
    (fun n => ((truncError T f (literalIndicator_machineThresholdCodeSeq parityFamily_codes)
        parityForecast_computable (by norm_num : (0 : ℚ) < 1 / 20)).luv n).expect
          (liaHistory (paperDP T)) n) ≈ₙ (fun _ => (0 : ℝ)) :=
  truncError_expect_tendsto_zero_of_UA T f (literalIndicator_machineThresholdCodeSeq parityFamily_codes)
    parityForecast_computable (by norm_num : (0 : ℚ) < 1 / 20) (parityForecast_UA T f hinj)

/-- **Corollary B.1 at the parity-tracking forecast**: per-day soft Total Trust at the forecast
gate `Ind_{1/20}(c_n > 2/5)` on the parity source, `E_n(⌜X_n û_n⌝) − (2/5)·E_n(⌜û_n⌝) ≳ₙ 0`.
N− for the content (decided source).
Source: vq-wiki-063 (Corollary B.1); round-2 adversarial audit N1
Kind: N−
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem parityForecast_corollaryB1 (f : DeferralFunction) (hinj : Function.Injective f.f) :
    (fun n => (meshProductLUV (forecastGate T parityForecast_computable (1 / 20) (2 / 5))
        (fun n => literalIndicator (parityFamily n)) n).expect (liaHistory (paperDP T)) n -
        ((2 / 5 : ℚ) : ℝ) *
          ((forecastGate T parityForecast_computable (1 / 20) (2 / 5)).luv n).expect
            (liaHistory (paperDP T)) n) ≳ₙ (fun _ => (0 : ℝ)) :=
  corollaryB1 T f hinj (literalIndicator_machineThresholdCodeSeq parityFamily_codes)
    (paritySource_valued T) parityForecast_computable (by norm_num : (0 : ℚ) < 1 / 20)
    (by norm_num : (0 : ℚ) ≤ 2 / 5) (parityForecast_UA T f hinj)

omit [Entailment.Consistent T] in
/-- The forecast gate of the parity-tracking forecast at `(δ, t) = (1/20, 2/5)` is valued, in
every completed-theory world, at the payout of the parity family: `Ind_{1/20}(1 > 2/5) = 1` on
even days (where the member is a theorem), `Ind_{1/20}(0 > 2/5) = 0` on odd days (where it is
refutable).
Source: none: infrastructure (witness); FAF `RationalQuoteCode.reflected`
Kind: L
Fidelity: n/a -/
theorem parityForecast_gate_valued (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt ((forecastGate T parityForecast_computable (1 / 20) (2 / 5)).luv n)
      (v.payout (parityFamily n)) := by
  have h := forecastGate_reflected T parityForecast_computable (1 / 20) (2 / 5) n v hv
  convert h using 1
  unfold PCWorld.payout parityFamily parityForecast
  by_cases hn : n % 2 = 0
  · have hT : v.Holds (tautAtom n) := holds_neg_contraAtom v n
    rw [if_pos hn, if_pos hn, if_pos hT]
    push_cast
    symm
    rw [ctsInd_eq_one_iff (by norm_num)]
    norm_num
  · have hF : ¬ v.Holds (contraAtom n) := (PCWorld.holds_neg v _).1 (holds_neg_contraAtom v n)
    rw [if_neg hn, if_neg hn, if_neg hF]
    push_cast
    symm
    rw [ctsInd_eq_zero_iff (by norm_num)]
    norm_num

/-- The expectation of the parity-tracking forecast gate is asymptotically the price of the
parity family: `E_n(⌜û_n⌝) ≈ₙ P_n(φ_n)` (the exact transfer lemma against the literal
indicator, both valued at the payout).
Source: none: infrastructure (witness); `Transfer.lean`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem parityForecast_gate_expect :
    (fun n => ((forecastGate T parityForecast_computable (1 / 20) (2 / 5)).luv n).expect
        (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => liaHistory (paperDP T) n (parityFamily n)) := by
  have h : (fun n => ((forecastGate T parityForecast_computable (1 / 20) (2 / 5)).luv n).expect
        (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (literalIndicator (parityFamily n)).expect (liaHistory (paperDP T)) n) :=
    expect_asympEq_of_reflected_exact
      (forecastGate T parityForecast_computable (1 / 20) (2 / 5)).poly
      (literalIndicator_machineThresholdCodeSeq parityFamily_codes)
      (fun n v => v.payout (parityFamily n))
      (fun n v hv => parityForecast_gate_valued T n v hv)
      (fun n v hv => literalIndicator_valuesAt (parityFamily n) (paperDP T) hv)
      (paperDP_hworld T)
  have h2 : (fun n => (literalIndicator (parityFamily n)).expect (liaHistory (paperDP T)) n) =
      (fun n => liaHistory (paperDP T) n (parityFamily n)) := by
    funext n
    rw [literalIndicator_expect]
  rwa [h2] at h

/-- **The gate expectation exceeds `3/4` infinitely often** (on all large even days, where the
member is a theorem and `thm:provind` drives its price to `1`).
Source: none: infrastructure (witness); FAF `lic_provind_true`
Kind: L
Fidelity: n/a -/
theorem parityForecast_gate_expect_frequently :
    ∃ᶠ n in atTop, (3 / 4 : ℝ) <
      ((forecastGate T parityForecast_computable (1 / 20) (2 / 5)).luv n).expect
        (liaHistory (paperDP T)) n := by
  have hT := lic_provind_true (liaHistory (paperDP T)) (paperDP T) tautAtom tautAtom_codes
    (fun n v _ => holds_neg_contraAtom v n) (paperDP_hworld T)
  have hT' : Tendsto (fun n => liaHistory (paperDP T) n (tautAtom n) - 1) atTop (𝓝 0) := hT
  have hE : Tendsto (fun n =>
      ((forecastGate T parityForecast_computable (1 / 20) (2 / 5)).luv n).expect
        (liaHistory (paperDP T)) n - liaHistory (paperDP T) n (parityFamily n)) atTop (𝓝 0) :=
    parityForecast_gate_expect T
  refine (frequently_even'.and_eventually
    ((hT'.eventually (lt_mem_nhds (by norm_num : (-(1 / 8) : ℝ) < 0))).and
      (hE.eventually (lt_mem_nhds (by norm_num : (-(1 / 8) : ℝ) < 0))))).mono ?_
  rintro n ⟨hn, h1, h2⟩
  have hpar : parityFamily n = tautAtom n := if_pos hn
  rw [hpar] at h2
  linarith

/-- **Theorem B's bound bites at the parity-tracking forecast**: its right-hand side
`(2/5)·E_n(⌜û_n⌝) − (7/5)·E_n(⌜e_n⌝)` exceeds `1/5` infinitely often (gate expectation `> 3/4`
on large even days, residual expectation `< 1/14` eventually) — so, unlike at Prop 6.3's data
(`theoremB_parity_instance`, right-hand side `→ −1`), the instance's conclusion is a genuine
lower bound on `E_n(⌜X_n û_n⌝)` on those days. The non-vacuity certificate of
`theoremB_parityForecast_instance`; the content is still `provind`-implied (decided source).
Source: round-2 fidelity audit B1 / adversarial audit B1 (ii) ("the bound bites")
Kind: N− (non-vacuity of the conclusion; content not exercised)
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem theoremB_parityForecast_bound_bites (f : DeferralFunction)
    (hinj : Function.Injective f.f) :
    ∃ᶠ n in atTop, (1 / 5 : ℝ) <
      ((2 / 5 : ℚ) : ℝ) *
          ((forecastGate T parityForecast_computable (1 / 20) (2 / 5)).luv n).expect
            (liaHistory (paperDP T)) n -
        (1 + ((2 / 5 : ℚ) : ℝ)) *
          ((truncError T f (literalIndicator_machineThresholdCodeSeq parityFamily_codes)
            parityForecast_computable (by norm_num : (0 : ℚ) < 1 / 20)).luv n).expect
              (liaHistory (paperDP T)) n := by
  have hres : Tendsto (fun n =>
      ((truncError T f (literalIndicator_machineThresholdCodeSeq parityFamily_codes)
        parityForecast_computable (by norm_num : (0 : ℚ) < 1 / 20)).luv n).expect
          (liaHistory (paperDP T)) n - 0) atTop (𝓝 0) :=
    parityForecast_residual_vanishes T f hinj
  refine ((parityForecast_gate_expect_frequently T).and_eventually
    (hres.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 14)))).mono ?_
  rintro n ⟨h1, h2⟩
  push_cast
  linarith

/-- The parity-tracking instances over `𝗣𝗔` at `succDeferral` (instance binders discharged; an
instantiability check, not a non-vacuity witness).
Source: mandate design decision 1
Kind: L
Fidelity: n/a -/
example : ∃ᶠ n in atTop, (1 / 5 : ℝ) <
      ((2 / 5 : ℚ) : ℝ) *
          ((forecastGate 𝗣𝗔 parityForecast_computable (1 / 20) (2 / 5)).luv n).expect
            (liaHistory (paperDP 𝗣𝗔)) n -
        (1 + ((2 / 5 : ℚ) : ℝ)) *
          ((truncError 𝗣𝗔 succDeferral (literalIndicator_machineThresholdCodeSeq parityFamily_codes)
            parityForecast_computable (by norm_num : (0 : ℚ) < 1 / 20)).luv n).expect
              (liaHistory (paperDP 𝗣𝗔)) n :=
  theoremB_parityForecast_bound_bites 𝗣𝗔 succDeferral succDeferral_injective

/-! ## The gated `est` at a non-constant generable gate -/

/-- The parity gate: the ramp of the deferred price of the parity source at `(δ, s) = (1/4, 1/2)`,
as a P-generable `[0,1]` weight (`estWeight`), read at the deferred day; not constant — `1` on
all large even days, `0` on all large odd days (`witnessGate`).
Source: round-2 adversarial audit N7 (a non-constant generable gate for
`gatedSelfTrust_productForm`)
Kind: D
Fidelity: n/a -/
def parityGate (f : DeferralFunction) : ℕ → ℚ :=
  estWeight T f (fun n => literalIndicator (parityFamily n)) (1 / 4) (1 / 2)

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The parity gate is P-generable.
Source: `Est.lean` `estWeight_pgenerable`
Kind: L
Fidelity: n/a -/
theorem parityGate_pgenerable (f : DeferralFunction) :
    PGenerableRat (liaHistory (paperDP T)) (parityGate T f) :=
  estWeight_pgenerable T f (literalIndicator_machineThresholdCodeSeq parityFamily_codes)
    (by norm_num : (0 : ℚ) < 1 / 4) (1 / 2)

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The parity gate lies in `[0,1]`.
Source: `Est.lean` `estWeight_mem`
Kind: L
Fidelity: n/a -/
theorem parityGate_mem (f : DeferralFunction) (m : ℕ) :
    0 ≤ parityGate T f m ∧ parityGate T f m ≤ 1 :=
  estWeight_mem T f _ (1 / 4) (1 / 2) m

/-- **The product gate `Ind_{1/4}(E_{f n}(X_n) > 1/2) · w_{f n}` at `w := parityGate` is `1`
infinitely often** (it is the square of the witness gate, `1` on all large even days).
Source: round-2 adversarial audit N7; `estWitness_gate_live`
Kind: L
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem gatedParity_gate_live (f : DeferralFunction) (hinj : Function.Injective f.f) :
    ∃ᶠ n in atTop,
      ((gatedWeight T f (fun n => literalIndicator (parityFamily n)) (1 / 4) (1 / 2)
        (parityGate T f) (f n) : ℚ) : ℝ) = 1 := by
  refine (estWitness_gate_live T f hinj).mono (fun n hn => ?_)
  unfold witnessGate at hn
  simp only [gatedWeight_at_cast T f hinj, parityGate, estWeight_at_cast T f hinj,
    literalIndicator_expect, hn]
  norm_num

/-- **The gated `est` at a non-constant generable gate**: `gatedSelfTrust_productForm` on the
parity source at `(δ, s) = (1/4, 1/2)` with the gate `w := parityGate` (the ramp of the deferred
price itself): `E_n(⌜X_n · Ind_{1/4}(E_{f n}(X_n) > 1/2) · w_{f n}⌝) − (1/2)·E_n(⌜Ind_{1/4}(…) ·
w_{f n}⌝) ≳ₙ 0`, the product gate being `1` on all large even days (`gatedParity_gate_live`).
**N− for the content**: the parity source is decided, so the bet is world-nonnegative without
`ccee` (as for `estWitness_est`); what the instance shows is that `gatedSelfTrust_productForm`
is inhabited at a gate that is neither `0` nor `1` identically.
Source: trust-lab-2-034 (i) (gated `st`); round-2 adversarial audit N7
Kind: N−
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem gatedSelfTrust_parity_instance (f : DeferralFunction) (hinj : Function.Injective f.f) :
    (fun n => (meshProductLUV (paperDeferredWeightQuoteCode T f
        (gatedWeight T f (fun n => literalIndicator (parityFamily n)) (1 / 4) (1 / 2)
          (parityGate T f))
        (gatedWeight_pgenerable T f (literalIndicator_machineThresholdCodeSeq parityFamily_codes)
          (by norm_num : (0 : ℚ) < 1 / 4) (1 / 2) (parityGate_pgenerable T f))
        (gatedWeight_mem T f _ (1 / 4) (1 / 2) (parityGate_mem T f)))
        (fun n => literalIndicator (parityFamily n)) n).expect (liaHistory (paperDP T)) n -
      ((1 / 2 : ℚ) : ℝ) * ((paperDeferredWeightQuoteCode T f
        (gatedWeight T f (fun n => literalIndicator (parityFamily n)) (1 / 4) (1 / 2)
          (parityGate T f))
        (gatedWeight_pgenerable T f (literalIndicator_machineThresholdCodeSeq parityFamily_codes)
          (by norm_num : (0 : ℚ) < 1 / 4) (1 / 2) (parityGate_pgenerable T f))
        (gatedWeight_mem T f _ (1 / 4) (1 / 2) (parityGate_mem T f))).luv n).expect
          (liaHistory (paperDP T)) n) ≳ₙ (fun _ => (0 : ℝ)) :=
  gatedSelfTrust_productForm T f hinj (literalIndicator_machineThresholdCodeSeq parityFamily_codes)
    (paritySource_valued T) (by norm_num : (0 : ℚ) < 1 / 4) (1 / 2) (parityGate_mem T f)
    (parityGate_pgenerable T f)

end

end Cleanroom.Deference.DefSelfTrust
