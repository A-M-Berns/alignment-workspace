import Cleanroom.Found.CorrThreeStep.Setting
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# `corr-caution-power` — Setting: the caution objects D1–D10 (definitions of record)

The `caution` thread of the 2026-09-14 corrigibility run (`dynamics/caution-final.md`) over
FAF's finite-probability carrier `FactoredSpaces.Distr` and `corr-three-step`'s `expect`:

* `CautionState` — D1's joint state at one time: value functions `V ω a`, the null action
  `nul`, the value posterior `P : Distr Ω`, the target `target : Ω` (the standing realizability
  assumption `ω* ∈ Ω` is *built into the type*; `harmOf` below is what survives its failure),
  and the trusted base `γ : Distr A` (D7);
* D2–D3 `proxy`, `err`, `Covered`, `coveredSet` — coverage is a relation between `P` and
  `target`, never a property of the agent alone (S1);
* D4–D5 `harmOf`, `harm`, `trueHarm`, `estHarm`, `baseHarm` (`R`), `estBaseHarm` (`R̂`),
  the predicates `ConservativelyCalibrated` (`R ≤ R̂`) and `Reckless` (`R̂ < R`) — **the ratio
  `ρ = R/R̂` is not defined** (junk at `R̂ = 0`, where S1's and S5(b)'s witnesses live);
  the Jensen split `estBaseHarm1 + estBaseHarm2` with `0 ≤ estBaseHarm2`;
* D6 self-suspicion as FAF's `Distr.mix` (a representation: `expect_mix`);
* D7–D8 `OP`, `qRule`, `qRuleFloored`, `realizedHarm`;
* D10's pointwise predicate `CoveredOrKnownUncovered` as the source states it, and the
  corrected `NullCoveredKnownUncovered` (the source's "including `∅`" clause is vacuous,
  see `coveredOrKnownUncovered_iff` and `CautionRule.lean`).

The S1 identities (T1(i)–(iii)) close the file; the S1 witnesses are in `Witnesses.lean`.
Trajectories (`COR`, `CORδ`) are in `CautionRule.lean`. D9 is `Reversibility.lean`'s.

Register: D5 ("reckless") and D10 are CLAUDE's formalizations of Abram's v2 §1.3 sentence
(`caution-final.md` §0: "the definition D5 below is CLAUDE's"); nothing here says what Abram
meant (ATTRIBUTION-UNVETTED applies to any such reading).

Sources: [[corr-wf14-inventory]] 095–103 → `caution-final.md` D1–D10 (l. 23–55), S1 (l. 61),
proof §1 (l. 113); [[corr-wf14-2-inventory]] 2-036 → `caution-adversary.md` A0.1–A0.2.
-/

namespace Cleanroom.Corrigibility.CorrCautionPower

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect expect_const

/-! ## Infrastructure on `expect` (not in `corr-three-step`) -/

section ExpectExtra

variable {Ω : Type*} [Fintype Ω]

/-- A constant minus a function: `E[k − X] = k − E[X]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma expect_const_sub (μ : Distr Ω) (k : ℝ) (X : Ω → ℝ) :
    expect μ (fun ω => k - X ω) = k - expect μ X := by
  rw [expect_sub, expect_const]

/-- Expectation under a point mass is evaluation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma expect_delta [DecidableEq Ω] (ω' : Ω) (X : Ω → ℝ) : expect (Distr.delta ω') X = X ω' := by
  classical
  simp [expect, Distr.delta_mass]

/-- Expectation under a mixture is the mixture of expectations.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma expect_mix (t : unitInterval) (P Q : Distr Ω) (X : Ω → ℝ) :
    expect (Distr.mix t P Q) X = (1 - (t : ℝ)) * expect P X + (t : ℝ) * expect Q X := by
  simp only [expect, Distr.mix, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun ω _ => by ring

/-- `max (E[X], 0) ≤ E[max (X, 0)]` (Jensen for the positive part).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma max_expect_zero_le (μ : Distr Ω) (X : Ω → ℝ) :
    max (expect μ X) 0 ≤ expect μ (fun ω => max (X ω) 0) := by
  refine max_le ?_ (expect_nonneg μ fun ω => le_max_right _ _)
  exact expect_mono μ fun ω => le_max_left _ _

end ExpectExtra

/-! ## D4: commission-only harm of an arbitrary value function -/

/-- **D4, for any value function.** `harmOf nul v a = (v nul − v a)⁺`: the harm of `a`
relative to the null action under the value function `v : A → ℝ` (Taylor 2016 §2.1's cost
with `noop` as reference). Commission only: `harmOf nul v nul = 0` by construction, so harms of
*omission* are invisible (source scope limitation, adversary A0.4). Stated for a bare
`v : A → ℝ`, not for `V ω`, so that a true value function *outside* the algebra `Ω`
(algebra misspecification) has a harm — this is what S4(a)'s robustness is stated over.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D4 (l. 35)
Kind: D
Fidelity: exact (`max (·) 0`, real-valued; no `ℝ≥0` truncation) -/
def harmOf {A : Type*} (nul : A) (v : A → ℝ) (a : A) : ℝ := max (v nul - v a) 0

/-- Harm is nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma harmOf_nonneg {A : Type*} (nul : A) (v : A → ℝ) (a : A) : 0 ≤ harmOf nul v a :=
  le_max_right _ _

/-- The null action has zero harm under every value function (commission only).
Source: [[corr-wf14-inventory]] 095 / caution-final.md D4 (l. 35)
Kind: L
Fidelity: exact -/
lemma harmOf_nul {A : Type*} (nul : A) (v : A → ℝ) : harmOf nul v nul = 0 := by
  simp [harmOf]

/-! ## D1: the joint state -/

/-- **D1, the joint state at one time** (minimal): value hypotheses `V ω : A → ℝ`, the null
action `nul` (D1's `∅`), the value posterior `P`, the target `target` (`ω*_t`) and the
trusted base `γ` (D7). **Realizability is built into the type:** `target : Ω` says the human
reflectively endorsed value hypothesis is *in* the algebra — D1's flagged standing assumption;
its failure (algebra misspecification) is modelled by stating S4 over `harmOf nul trueV` for a
`trueV : A → ℝ` that is not any `V ω`. D1's range `V ω a ∈ [0, 1]` is the hypothesis `InRange`,
never a field. The constants `η`, `qmin`, `δ`, `λ` are parameters of the theorems.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D1 (l. 25), D7 (l. 43)
Kind: D
Fidelity: variant: one time step, no oversight state `(α, β)`, no growth `A_{t+1} ⊋ A_t`
Hyps: n/a (definition) -/
structure CautionState (A Ω : Type*) [Fintype A] [Fintype Ω] where
  /-- The value hypotheses. -/
  V : Ω → A → ℝ
  /-- The null action `∅`. -/
  nul : A
  /-- The value posterior. -/
  P : Distr Ω
  /-- The target `ω*` (realizability built in). -/
  target : Ω
  /-- The trusted base distribution. -/
  γ : Distr A

namespace CautionState

variable {A Ω : Type*} [Fintype A] [Fintype Ω] (S : CautionState A Ω)

/-- D1's range assumption `V_ω : A → [0, 1]`, as a predicate.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D1 (l. 25)
Kind: D
Fidelity: exact -/
def InRange : Prop := ∀ ω a, S.V ω a ∈ Set.Icc (0 : ℝ) 1

/-! ### D2–D3: proxy, coverage error, coverage -/

/-- **D2, the proxy** `U(a) = E_P[V_ω(a)]` (the linear-expectation proxy).
Source: [[corr-wf14-inventory]] 095 / caution-final.md D2 (l. 29)
Kind: D
Fidelity: exact -/
noncomputable def proxy (a : A) : ℝ := expect S.P (fun ω => S.V ω a)

/-- **D2, the coverage error** `e(a) = U(a) − V_{ω*}(a)`.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D2 (l. 29)
Kind: D
Fidelity: exact -/
noncomputable def err (a : A) : ℝ := S.proxy a - S.V S.target a

/-- **D3, δ-coverage** `|e(a)| ≤ δ`: a *relation between `P` and `target`* (third-person, S1),
not a property of the agent's state alone.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D3 (l. 31)
Kind: D
Fidelity: exact -/
def Covered (δ : ℝ) (a : A) : Prop := |S.err a| ≤ δ

open scoped Classical in
/-- **D3, the covered set** `C(δ)` as a `Finset`.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D3 (l. 31)
Kind: D
Fidelity: exact -/
noncomputable def coveredSet (δ : ℝ) : Finset A := univ.filter (fun a => |S.err a| ≤ δ)

/-- Membership in the covered set. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_coveredSet {δ : ℝ} {a : A} : a ∈ S.coveredSet δ ↔ S.Covered δ a := by
  classical
  simp [coveredSet, Covered]

/-! ### D4–D5: harm, estimated harm, base harm -/

/-- **D4, harm under hypothesis `ω`**: `c_ω(a) = (V_ω(∅) − V_ω(a))⁺`.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D4 (l. 35)
Kind: D
Fidelity: exact -/
noncomputable def harm (ω : Ω) (a : A) : ℝ := harmOf S.nul (S.V ω) a

/-- **D4, true harm** `c(a) = c_{ω*}(a)`.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D4 (l. 35)
Kind: D
Fidelity: exact -/
noncomputable def trueHarm (a : A) : ℝ := S.harm S.target a

/-- **D4, estimated harm** `ĉ(a) = E_P[c_ω(a)]`.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D4 (l. 35)
Kind: D
Fidelity: exact -/
noncomputable def estHarm (a : A) : ℝ := expect S.P (fun ω => S.harm ω a)

/-- The `ω`-indexed base harm `E_{a∼γ}[c_ω(a)]` (the quantity whose `P`-expectation is `R̂`).
Source: [[corr-wf14-inventory]] 095 / caution-final.md D5 (l. 37), proof §1 (l. 113)
Kind: D
Fidelity: exact -/
noncomputable def baseHarmOf (ω : Ω) : ℝ := expect S.γ (S.harm ω)

/-- **D5, base harm** `R = E_{a∼γ}[c(a)]` (true harm of the base).
Source: [[corr-wf14-inventory]] 095 / caution-final.md D5 (l. 37)
Kind: D
Fidelity: exact -/
noncomputable def baseHarm : ℝ := expect S.γ S.trueHarm

/-- **D5, estimated base harm** `R̂ = E_{a∼γ}[ĉ(a)]` — a *first-order* functional of `P`
(the believed harm of human-like actions; adversary A0.1, accepted by the source).
Source: [[corr-wf14-inventory]] 095 / caution-final.md D5 (l. 37)
Kind: D
Fidelity: exact -/
noncomputable def estBaseHarm : ℝ := expect S.γ S.estHarm

/-- **D5, conservatively calibrated about base harm:** `R ≤ R̂` (the source's `ρ ≤ 1`, written
without the ratio — `ρ = R/R̂` has a junk value at `R̂ = 0`).
Source: [[corr-wf14-inventory]] 095 / caution-final.md D5 (l. 37)
Kind: D
Fidelity: variant: predicate form of `ρ ≤ 1` (agrees with the source under `0 < R̂`; at `R̂ = 0` the source's convention `ρ = +∞` if `R > 0`, `1` if `R = 0` agrees too) -/
def ConservativelyCalibrated : Prop := S.baseHarm ≤ S.estBaseHarm

/-- **D5, reckless:** `R̂ < R` (the source's `ρ > 1`). CLAUDE's definition, not Abram's.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D5 (l. 37), §0 (l. 19)
Kind: D
Fidelity: variant: predicate form of `ρ > 1` -/
def Reckless : Prop := S.estBaseHarm < S.baseHarm

/-- The proxy's own view of harm `(U(∅) − U(a))⁺`.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D5 (l. 37, `R̂⁽¹⁾`'s integrand)
Kind: D
Fidelity: exact -/
noncomputable def proxyHarm (a : A) : ℝ := max (S.proxy S.nul - S.proxy a) 0

/-- **D5, the Jensen split (first part)** `R̂⁽¹⁾ = E_γ[(U(∅) − U(a))⁺]`.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D5 (l. 37)
Kind: D
Fidelity: exact -/
noncomputable def estBaseHarm1 : ℝ := expect S.γ S.proxyHarm

/-- **D5, the Jensen split (second part)** `R̂⁽²⁾ = R̂ − R̂⁽¹⁾`.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D5 (l. 37)
Kind: D
Fidelity: exact -/
noncomputable def estBaseHarm2 : ℝ := S.estBaseHarm - S.estBaseHarm1

/-- **Jensen:** the proxy's harm is at most the estimated harm, `(U(∅) − U(a))⁺ ≤ ĉ(a)`.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D5 (l. 37), proof §5 (l. 129)
Kind: L
Fidelity: exact -/
lemma proxyHarm_le_estHarm (a : A) : S.proxyHarm a ≤ S.estHarm a := by
  unfold proxyHarm estHarm harm harmOf proxy
  rw [← expect_sub]
  exact max_expect_zero_le S.P _

/-- **D5:** `0 ≤ R̂⁽²⁾` — the honest residue of "second-order": posterior disagreement about
harm, still a functional of `P`.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D5 (l. 37)
Kind: L
Fidelity: exact -/
lemma estBaseHarm2_nonneg : 0 ≤ S.estBaseHarm2 := by
  unfold estBaseHarm2 estBaseHarm estBaseHarm1
  rw [sub_nonneg]
  exact expect_mono S.γ fun a => S.proxyHarm_le_estHarm a

/-- Harm under any hypothesis is nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma harm_nonneg (ω : Ω) (a : A) : 0 ≤ S.harm ω a := harmOf_nonneg _ _ _

/-- True harm is nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma trueHarm_nonneg (a : A) : 0 ≤ S.trueHarm a := harmOf_nonneg _ _ _

/-- Estimated harm is nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma estHarm_nonneg (a : A) : 0 ≤ S.estHarm a :=
  expect_nonneg S.P fun ω => S.harm_nonneg ω a

/-- The null action's true harm is `0`; so is its estimated harm.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D4 (l. 35)
Kind: L
Fidelity: exact -/
lemma trueHarm_nul : S.trueHarm S.nul = 0 := harmOf_nul _ _

/-- The null action's estimated harm is `0`.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D4 (l. 35)
Kind: L
Fidelity: exact -/
lemma estHarm_nul : S.estHarm S.nul = 0 := by
  unfold estHarm harm
  simp only [harmOf_nul]
  exact expect_const S.P 0

/-- Base harm is nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma baseHarm_nonneg : 0 ≤ S.baseHarm := expect_nonneg S.γ S.trueHarm_nonneg

/-- Estimated base harm is nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma estBaseHarm_nonneg : 0 ≤ S.estBaseHarm := expect_nonneg S.γ S.estHarm_nonneg

/-! ### D8: realized harm; D10: the pointwise predicate -/

/-- **D8, realized harm** `H = E_{a∼π}[c(a)]` of any action distribution `π`.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D8 (l. 45)
Kind: D
Fidelity: exact -/
noncomputable def realizedHarm (π : Distr A) : ℝ := expect π S.trueHarm

/-- **D10, the pointwise predicate as the source states it:** for every `a ∈ supp γ` *and* the
null action, `a` is δ-covered **or** known-uncovered (`c(a) ≤ ĉ(a)`). **Warning (finding):** at
`a = nul` the second disjunct is `0 ≤ 0`, so the "including `∅`" clause is vacuous
(`coveredOrKnownUncovered_iff`); the source's proof of S5(b) uses `∅ ∈ C(δ)`, which this
predicate does not supply. The corrected predicate is `NullCoveredKnownUncovered`.
Source: [[corr-wf14-inventory]] 097 / caution-final.md D10 pointwise form (l. 55)
Kind: D
Fidelity: exact (as printed; see the warning) -/
def CoveredOrKnownUncovered (δ : ℝ) : Prop :=
  ∀ a, (a ∈ S.γ.support ∨ a = S.nul) → S.Covered δ a ∨ S.trueHarm a ≤ S.estHarm a

/-- **D10, corrected pointwise predicate:** the null action is δ-covered, and every `a ∈ supp γ`
is δ-covered or known-uncovered. This is what the source's S5(b) proof actually uses.
Source: [[corr-wf14-inventory]] 097 / caution-final.md D10 (l. 55), proof §5 (l. 129, "using `∅ ∈ C_t`")
Kind: D
Fidelity: variant: `∅ ∈ C(δ)` stated as coverage, not as the vacuous disjunction -/
def NullCoveredKnownUncovered (δ : ℝ) : Prop :=
  S.Covered δ S.nul ∧ ∀ a ∈ S.γ.support, S.Covered δ a ∨ S.trueHarm a ≤ S.estHarm a

/-- **The null clause of D10's printed predicate is vacuous:** the predicate holds iff it holds
on `supp γ` alone, because `c(∅) = 0 = ĉ(∅)`.
Source: [[corr-wf14-inventory]] 097 / caution-final.md D10 (l. 55) — finding
Kind: L
Fidelity: exact -/
lemma coveredOrKnownUncovered_iff (δ : ℝ) :
    S.CoveredOrKnownUncovered δ ↔
      ∀ a ∈ S.γ.support, S.Covered δ a ∨ S.trueHarm a ≤ S.estHarm a := by
  constructor
  · intro h a ha; exact h a (Or.inl ha)
  · intro h a ha
    rcases ha with ha | rfl
    · exact h a ha
    · right; rw [S.trueHarm_nul, S.estHarm_nul]

/-- The corrected predicate implies the printed one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma coveredOrKnownUncovered_of_nullCovered {δ : ℝ} (h : S.NullCoveredKnownUncovered δ) :
    S.CoveredOrKnownUncovered δ :=
  (S.coveredOrKnownUncovered_iff δ).2 h.2

/-! ### T1 — S1: the identities (Kind L; the witnesses are in `Witnesses.lean`) -/

/-- **S1(i), identity:** `E_P[U(a) − V_ω(a)] = 0` — every posterior expects its own proxy to be
exact.
Source: [[corr-wf14-inventory]] 095 / caution-final.md S1 (l. 61), proof §1 (l. 113)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem expect_proxy_sub_V (a : A) : expect S.P (fun ω => S.proxy a - S.V ω a) = 0 := by
  rw [expect_const_sub]; simp [proxy]

/-- **S1(ii), identity:** `E_P[R_ω] = R̂` — the `P`-expectation of the `ω`-indexed base harm is
the estimate: "every agent expects itself calibrated" (under the standing assumption that `P`
is a posterior *about* the target).
Source: [[corr-wf14-inventory]] 095 / caution-final.md S1 (l. 61), proof §1 (l. 113)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem expect_baseHarmOf : expect S.P S.baseHarmOf = S.estBaseHarm := by
  unfold baseHarmOf estBaseHarm estHarm expect
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun a _ => sum_congr rfl fun ω _ => by ring

/-- **2-036(a), identity:** at a point-mass posterior `δ_{ω'}` the estimated base harm is the base
harm *under `ω'`* — `R̂` is driven by the content of the point estimate, not by any uncertainty
about it (adversary A0.1).
Source: [[corr-wf14-2-inventory]] 2-036 / caution-adversary.md A0.1 (l. 17)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem estBaseHarm_of_delta [DecidableEq Ω] {ω' : Ω} (h : S.P = Distr.delta ω') :
    S.estBaseHarm = S.baseHarmOf ω' := by
  unfold estBaseHarm baseHarmOf estHarm
  rw [h]
  simp only [expect_delta]

end CautionState

/-! ## D6: self-suspicion; D7–D8: optimization power and the caution rules -/

/-- **D6, self-suspicion as a mixture** `P = (1 − μ) Pᶜ + μ Pʷ` (FAF's `Distr.mix`): a
*representation*, not a new object.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D6 (l. 39)
Kind: D
Fidelity: exact -/
noncomputable def selfSuspicion {Ω : Type*} [Fintype Ω] (μ : unitInterval) (Pc Pw : Distr Ω) :
    Distr Ω := Distr.mix μ Pc Pw

/-- **D6, collapse:** a one-shot expectation under the self-suspicious posterior is the
`μ`-mixture of the expectations — only the mixture matters.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D6 (l. 39, "for a one-shot decision only the mixture matters")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem expect_selfSuspicion {Ω : Type*} [Fintype Ω] (μ : unitInterval) (Pc Pw : Distr Ω)
    (X : Ω → ℝ) :
    expect (selfSuspicion μ Pc Pw) X = (1 - (μ : ℝ)) * expect Pc X + (μ : ℝ) * expect Pw X :=
  expect_mix μ Pc Pw X

/-- **D7, optimization power** `OP(q) = log(1/q)` nats of selection over the base.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D7 (l. 43)
Kind: D
Fidelity: exact (at `q = 0` Lean gives `log 0 = 0`, not `+∞`; every use carries `0 < q`) -/
noncomputable def OP (q : ℝ) : ℝ := Real.log (1 / q)

/-- **D8, the caution rule's slice** `q = min{1, R̂/η}`. Junk-value watch: at `R̂ = 0` this is
`0` and the quantilizer at `q = 0` is *not defined* (`Quantilizer.lean` requires `0 < q`); the
source's "maximizer limit" is a limit, not a value.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D8 (l. 45)
Kind: D
Fidelity: exact -/
noncomputable def qRule (η Rhat : ℝ) : ℝ := min 1 (Rhat / η)

/-- **D8′, the floored caution rule's slice** `q = max{q_min, min{1, R̂/η}}`; always in
`[q_min, 1]` for `0 < q_min ≤ 1`, whatever `R̂` is — this is what buys S4(c)'s unconditional
bound at the price of the fixed object `q_min`.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D8′ (l. 45)
Kind: D
Fidelity: exact -/
noncomputable def qRuleFloored (qmin η Rhat : ℝ) : ℝ := max qmin (min 1 (Rhat / η))

/-- `qRule ≤ 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma qRule_le_one (η Rhat : ℝ) : qRule η Rhat ≤ 1 := min_le_left _ _

/-- `0 < qRule` under `0 < η`, `0 < R̂`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma qRule_pos {η Rhat : ℝ} (hη : 0 < η) (hR : 0 < Rhat) : 0 < qRule η Rhat :=
  lt_min one_pos (div_pos hR hη)

/-- `qRuleFloored ≤ 1` under `q_min ≤ 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma qRuleFloored_le_one {qmin : ℝ} (hq : qmin ≤ 1) (η Rhat : ℝ) : qRuleFloored qmin η Rhat ≤ 1 :=
  max_le hq (min_le_left _ _)

/-- `q_min ≤ qRuleFloored`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma le_qRuleFloored (qmin η Rhat : ℝ) : qmin ≤ qRuleFloored qmin η Rhat := le_max_left _ _

/-- `0 < qRuleFloored` under `0 < q_min`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma qRuleFloored_pos {qmin : ℝ} (hq : 0 < qmin) (η Rhat : ℝ) : 0 < qRuleFloored qmin η Rhat :=
  lt_of_lt_of_le hq (le_qRuleFloored _ _ _)

/-- The floored rule lies above the unfloored one. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma qRule_le_qRuleFloored (qmin η Rhat : ℝ) : qRule η Rhat ≤ qRuleFloored qmin η Rhat :=
  le_max_right _ _

end Cleanroom.Corrigibility.CorrCautionPower
