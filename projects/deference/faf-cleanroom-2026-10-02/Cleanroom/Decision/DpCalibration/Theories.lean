import Cleanroom.Decision.DpCalibration.Limit
import Cleanroom.Decision.DpCalibration.Recording
import Cleanroom.Found.DpCoreTree.Nodes
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Theories, procedures, abstract problems, and the device taxonomy — definitions of record

T14, T15(a), T16(a) and T6 of [[dp-calibration-mandate]].

* `uniformOn`, `argmaxPlus`, `edtProc` — Definition 17's `EDT` (uniform over
  `argmax_{A_d^+} V_{s_d}(a)`, `Unif(A_d)` on an empty domain); `TEdt` — Definition 18's
  advocacy theory `T_EDT` (`supp C(d) ⊆ argmax_{A_d^+} V_{s_d}` at every queried point, no
  constraint where `A_d^+ = ∅`); `TOpt` — `T_opt` as `∀ C', V_B(C') ≤ V_B(C)` (no `sSup`).
* `tEdt_edtProc`, `edtProc_zeroRespecting` — `T_EDT(EDT, B)` for every `B`; `EDT` is
  zero-respecting (Definition 17's "by construction").
* `tEdtAt_of_deterministic_recorded` — **Remark 3.9's theorem-let, precise form** (T6): at a
  recorded point with `ν(O_d) > 0`, a deterministic strictly calibrated procedure satisfies the
  `T_EDT` clause there (with `A_d^+ = {C(d)}`); v2's "approves every deterministic procedure" is
  true only at such points (findings).
* `Instance`, `AbstractProblem`, `Sense`, `IsCalibrated`, `Consistent`, `MakesInconsistent`,
  `TrembleConsistent` — Definitions 14–16 and Remark 3.12 (Σ-typed).
* The **devices**, named apart: `EventTrembleEdtConsistent` (D2, FR-11's hypothesis),
  `LimitStateEdt` (D1), `AdviceEdt` (D4), `OccTrembleEdtConsistent` (D3, with `D3⁰`),
  `TestSeqTrembleEdtConsistent` (DY-3). `Dev` (Definition 22) is `dp-local-opt`'s and is not
  defined here.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-! ## Definition 17: the EDT procedure; Definition 18: `T_EDT`, `T_opt` -/

section procedures

/-- The uniform distribution on a nonempty finite set of actions (the "uniform mixture over an
argmax set" convention of Definition 17).
Source: [[decision-problems-v2]] §4 Definition 17 ("an argmax set becomes a mixed action by
uniform mixture")
Kind: D -/
def uniformOn {α : Type} [Fintype α] [DecidableEq α] (S : Finset α) (h : S.Nonempty) :
    FinDistr K α where
  w a := if a ∈ S then (S.card : K)⁻¹ else 0
  nonneg a := by split_ifs <;> simp
  sum_one := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul]
    have : (S.card : K) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr h).ne'
    exact mul_inv_cancel₀ this

/-- Weights of `uniformOn`. Source: none: infrastructure. Kind: L -/
@[simp] theorem uniformOn_w {α : Type} [Fintype α] [DecidableEq α] (S : Finset α) (h : S.Nonempty)
    (a : α) : (uniformOn (K := K) S h).w a = if a ∈ S then (S.card : K)⁻¹ else 0 := rfl

variable (s : ι → State Ω K) (actEv : (d : ι) → acts d → Finset Ω)

/-- `argmax_{a ∈ A_d^+} V_{s_d}(a)`: the subjectively possible actions of maximal news value.
Source: [[decision-problems-v2]] §4 Definition 17 (`EDT(d)`), Definition 18 (`T_EDT`)
Kind: D -/
def argmaxPlus (d : ι) : Finset (acts d) :=
  (APlus s actEv d).filter fun a => ∀ b ∈ APlus s actEv d, (s d).V (actEv d b) ≤ (s d).V (actEv d a)

/-- Membership in `argmaxPlus`. Source: none: infrastructure. Kind: L -/
theorem mem_argmaxPlus (d : ι) (a : acts d) :
    a ∈ argmaxPlus s actEv d ↔
      a ∈ APlus s actEv d ∧ ∀ b ∈ APlus s actEv d, (s d).V (actEv d b) ≤ (s d).V (actEv d a) := by
  simp [argmaxPlus]

/-- `argmaxPlus ⊆ A_d^+`. Source: none: infrastructure. Kind: L -/
theorem argmaxPlus_subset (d : ι) : argmaxPlus s actEv d ⊆ APlus s actEv d :=
  Finset.filter_subset _ _

/-- The argmax over a nonempty `A_d^+` is nonempty (a finite set has a maximiser).
Source: none: infrastructure. Kind: L -/
theorem argmaxPlus_nonempty (d : ι) (h : (APlus s actEv d).Nonempty) :
    (argmaxPlus s actEv d).Nonempty := by
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image (APlus s actEv d)
    (fun a => (s d).V (actEv d a)) h
  exact ⟨a, (mem_argmaxPlus s actEv d a).mpr ⟨ha, hmax⟩⟩

/-- **Definition 17's `EDT` procedure**: `Unif(argmax_{A_d^+} V_{s_d}(a))`, and `Unif(A_d)` when
`A_d^+ = ∅`.
Source: [[decision-problems-v2]] §4 Definition 17
Kind: D
Fidelity: exact -/
def edtProc [∀ d, Nonempty (acts d)] : Proc ι acts K := fun d =>
  if h : (argmaxPlus s actEv d).Nonempty then uniformOn (argmaxPlus s actEv d) h
  else FinDistr.uniform

/-- **Definition 18's `T_EDT` (advocacy)**: at every queried point with `A_d^+ ≠ ∅`,
`supp C(d) ⊆ argmax_{A_d^+} V_{s_d}`; no constraint where `A_d^+ = ∅`.
Source: [[decision-problems-v2]] §4 Definition 18
Kind: D
Fidelity: exact -/
def TEdt (C : Proc ι acts K) (B : Tree Ω ι acts K) : Prop :=
  ∀ d ∈ queried B, (APlus s actEv d).Nonempty → ∀ a, 0 < (C d).w a → a ∈ argmaxPlus s actEv d

/-- The `T_EDT` clause at one point. Source: [[decision-problems-v2]] Definition 18. Kind: D -/
def TEdtAt (C : Proc ι acts K) (d : ι) : Prop :=
  (APlus s actEv d).Nonempty → ∀ a, 0 < (C d).w a → a ∈ argmaxPlus s actEv d

/-- **Definition 18's `T_opt`**: `C` attains the maximal value on `B`, stated as
`∀ C', V_B(C') ≤ V_B(C)` (no supremum junk).
Source: [[decision-problems-v2]] §4 Definition 18 ("`T_opt(C, B)` holds iff `V_B(C) = max_{C'} V_B(C')`")
Kind: D
Fidelity: exact -/
def TOpt (C : Proc ι acts K) (B : Tree Ω ι acts K) : Prop := ∀ C', value C' B ≤ value C B

/-- **`T_EDT(EDT, B)` for every `B`**: the uniform-tie procedure is a canonical witness.
Source: [[decision-problems-v2]] §4 Definition 18 ("`T_EDT(EDT, B)` for every `B`")
Kind: L
Fidelity: exact -/
theorem tEdt_edtProc [∀ d, Nonempty (acts d)] (B : Tree Ω ι acts K) :
    TEdt s actEv (edtProc s actEv) B := by
  intro d _ hne a ha
  have hne' := argmaxPlus_nonempty s actEv d hne
  simp only [edtProc, dif_pos hne', uniformOn_w] at ha
  by_contra hc
  rw [if_neg hc] at ha
  exact lt_irrefl 0 ha

/-- **`EDT` is zero-respecting** (Definition 12), by construction: its support lies in the
argmax over `A_d^+ ⊆ A_d^+`.
Source: [[decision-problems-v2]] §4 Definition 17 ("EDT is zero-respecting by construction")
Kind: L
Fidelity: exact -/
theorem edtProc_zeroRespecting [∀ d, Nonempty (acts d)] :
    ZeroRespecting s actEv (edtProc s actEv) := by
  intro d hne a ha
  have hne' := argmaxPlus_nonempty s actEv d hne
  simp only [edtProc, dif_pos hne', uniformOn_w] at ha
  by_contra hc
  by_cases hmem : a ∈ argmaxPlus s actEv d
  · exact hc (argmaxPlus_subset s actEv d hmem)
  · rw [if_neg hmem] at ha; exact lt_irrefl 0 ha

/-- **Remark 3.9's theorem-let, precise form (T6)**: for a deterministic `C(d) = δ_{a₀}`, at a
point where `B` records for `C`, `ν(O_d) > 0` and strict OC holds, `A_d^+ = {a₀}` and the `T_EDT`
clause holds at `d`. v2 says `T_EDT` "approves *every* deterministic procedure" on such problems;
that is true only at points with `ν(O_d) > 0` (elsewhere the state is unconstrained and may fail
`T_EDT`), which is why this is stated per point with the positivity (findings).
Source: [[decision-problems-v2]] §3.1 Remark 3.9 ("`A_d^+ = {C(d)}`, so `T_EDT` approves every
deterministic procedure")
Kind: C
Fidelity: weaker: per point, with the positivity guard v2 omits
Hyps: (a) recording (Definition 7), (a) `0 < ν(O_d)`, (a) strict OC at `d`, (a) `C d = δ_{a₀}` -/
theorem tEdtAt_of_deterministic_recorded (obs : ι → Finset Ω) (C : Proc ι acts K)
    (B : Tree Ω ι acts K) {d : ι} (a₀ : acts d) (hC : C d = FinDistr.pure a₀)
    (h : RecordsFor obs actEv C B d) (hpos : 0 < nu C B (obs d)) (hs : StrictOCAt s obs C B d) :
    APlus s actEv d = {a₀} ∧ TEdtAt s actEv C d := by
  have hA := aPlus_eq_singleton_of_deterministic obs actEv C B s a₀ hC h hpos hs
  refine ⟨hA, fun _ a ha => ?_⟩
  rw [hC, FinDistr.pure_w] at ha
  have haa : a = a₀ := by
    by_contra hne; rw [if_neg hne] at ha; exact lt_irrefl 0 ha
  subst haa
  rw [mem_argmaxPlus, hA]
  refine ⟨Finset.mem_singleton_self a, fun b hb => ?_⟩
  rw [Finset.mem_singleton] at hb
  rw [hb]

end procedures

/-! ## Definitions 14–16 and Remark 3.12: abstract problems, consistency, tremble-consistency -/

section abstractProblems

/-- An *instantiation*: a concrete tree together with a state assignment.
Source: [[decision-problems-v2]] §3.2 Definition 14 ("a member `B ∈ Σ` is an instantiation")
Kind: D -/
structure Instance (Ω ι : Type) [Fintype Ω] [DecidableEq Ω] (acts : ι → Type) (K : Type)
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  /-- The concrete tree. -/
  B : Tree Ω ι acts K
  /-- The state assignment. -/
  s : ι → State Ω K

/-- **Definition 14: an abstract decision problem** is a set of instantiations.
Source: [[decision-problems-v2]] §3.2 Definition 14
Kind: D
Fidelity: exact (observations and action events are shared, being part of the points) -/
abbrev AbstractProblem (Ω ι : Type) [Fintype Ω] [DecidableEq Ω] (acts : ι → Type) (K : Type)
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] : Type :=
  Set (Instance Ω ι acts K)

/-- The five calibration senses of Definition 15.
Source: [[decision-problems-v2]] §3.2 Definition 15
Kind: D -/
inductive Sense : Type
  | strict
  | masked
  | limit
  | perRun
  | perOcc
  deriving DecidableEq

/-- `κ`-calibration as a predicate (masked = the definition of record, LF/vacuity).
Source: [[decision-problems-v2]] §3.2 Definition 15
Kind: D -/
def IsCalibrated [∀ d, Nonempty (acts d)] (κ : Sense) (obs : ι → Finset Ω) (s : ι → State Ω K)
    (C : Proc ι acts K) (B : Tree Ω ι acts K) : Prop :=
  match κ with
  | .strict => StrictOC s obs C B
  | .masked => MaskedOC s obs C B
  | .limit => LimitOC s obs C B
  | .perRun => PerRunSSC s C B
  | .perOcc => PerOccSSC s C B

/-- **Definition 15: `Σ` is `κ`-consistent for `C`** if some instantiation is `κ`-calibrated for
`C`.
Source: [[decision-problems-v2]] §3.2 Definition 15
Kind: D
Fidelity: exact -/
def Consistent [∀ d, Nonempty (acts d)] (κ : Sense) (obs : ι → Finset Ω)
    (AP : AbstractProblem Ω ι acts K) (C : Proc ι acts K) : Prop :=
  ∃ I ∈ AP, IsCalibrated κ obs I.s C I.B

/-- **Definition 16: `C` makes `X` `δ`-inconsistent in `Σ`** (at sense `κ`) if every
`κ`-calibrated instantiation has `ν_{B,C}(X) ≤ δ`.
Source: [[decision-problems-v2]] §3.2 Definition 16
Kind: D
Fidelity: exact -/
def MakesInconsistent [∀ d, Nonempty (acts d)] (κ : Sense) (obs : ι → Finset Ω)
    (AP : AbstractProblem Ω ι acts K) (C : Proc ι acts K) (X : Finset Ω) (δ : K) : Prop :=
  ∀ I ∈ AP, IsCalibrated κ obs I.s C I.B → nu C I.B X ≤ δ

/-- **Remark 3.12: `Σ` is tremble-consistent for `C` with respect to a theory `T`** (Σ-typed):
for every sufficiently small `ε > 0` some instantiation is strictly calibrated for `C^ε` and
`T(C, ·)` holds on it.
Source: [[decision-problems-v2]] §3.2 Remark 3.12
Kind: D
Fidelity: exact -/
def TrembleConsistent [∀ d, Nonempty (acts d)] (obs : ι → Finset Ω)
    (AP : AbstractProblem Ω ι acts K) (C : Proc ι acts K)
    (T : Proc ι acts K → Instance Ω ι acts K → Prop) : Prop :=
  ∃ ε₀ > (0 : K), ∀ ε, ∀ (h0 : 0 < ε) (h1 : ε ≤ 1), ε < ε₀ →
    ∃ I ∈ AP, StrictOC I.s obs (tremble C ε h0.le h1) I.B ∧ T C I

end abstractProblems

/-! ## The device taxonomy (T16(a)) -/

section devices

variable [∀ d, Nonempty (acts d)] (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
  (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **D2, event-tremble-EDT-consistency** (FR-11's hypothesis; Remark 3.12 applied to the
concrete tree with states bypassed): for all sufficiently small `ε > 0`, at every queried `d`
whose observation is tremble-realizable and at which some action event is realized within `O_d`
under `C^ε` (`A_d^+(ε) ≠ ∅`), `supp C(d) ⊆ argmax_{a : ν_ε(a ∧ O_d) > 0} 𝔼_ε[r | a ∧ O_d]`.
No `∃ s` is needed: where `ν_ε(O_d) > 0` the strictly calibrated state for `C^ε` is unique modulo
junk (`strictClausesAt_unique`), so its act values are the conditionals written here. The
conditional expectation is written with `condExp`; its guard `0 < ν_ε(a ∧ O_d)` is explicit for
every act compared. The escape clause `(∃ b, 0 < ν_ε(b ∧ O_d)) →` is Definition 18's "no
constraint where `A_d^+ = ∅`", which the advocacy predicate `T_EDT(C, B_ε)` in FR-11 carries
(added in repair round 1: without it a queried point whose action events miss every leaf-world
made D2 unsatisfiable for every procedure, and the OPEN existence row false). With the escape
clause the guard `nuPoly C B (obs d) ≠ 0` is redundant (if `nuPoly O_d = 0` then
`ν_ε(b ∧ O_d) = 0` for every `b` and the escape clause fires); it is kept for readability, as
the definition's "tremble-realizable `O_d`" domain (audit round 2, N7).
Source: `cf-workflow/phase1/fair-repair.md` FR-11; `calibration.md` "Tremble-EDT-consistency
(concrete)" and Devices (D2); [[decision-problems-v2]] §4 Definition 18 (the escape clause)
Kind: D
Fidelity: exact (domain convention: acts compared are those with `ν_ε(a ∧ O_d) > 0`; no
constraint where none has) -/
def EventTrembleEdtConsistent : Prop :=
  ∃ ε₀ > (0 : K), ∀ ε, ∀ (h0 : 0 < ε) (h1 : ε ≤ 1), ε < ε₀ →
    ∀ d ∈ queried B, nuPoly C B (obs d) ≠ 0 →
      (∃ b, 0 < nu (tremble C ε h0.le h1) B (actEv d b ∩ obs d)) → ∀ a, 0 < (C d).w a →
      0 < nu (tremble C ε h0.le h1) B (actEv d a ∩ obs d) ∧
      ∀ b, 0 < nu (tremble C ε h0.le h1) B (actEv d b ∩ obs d) →
        condExp (tremble C ε h0.le h1) B (actEv d b ∩ obs d) ≤
          condExp (tremble C ε h0.le h1) B (actEv d a ∩ obs d)

/-- **D1, limit-state EDT**: Definition 10's limit-calibrated states with `T_EDT` (Definition
18's domain `A_d^+` read off the limit state).
Source: `calibration.md` Devices (D1)
Kind: D -/
def LimitStateEdt (s : ι → State Ω K) : Prop := LimitOC s obs C B ∧ TEdt s actEv C B

/-- The limiting conditional act value `lim_{ε→0⁺} 𝔼_ε[r | Y]`, algebraically: the quotient of
the coefficients of `ε^{k'}` of `payPoly Y` and `nuPoly Y`, `k'` the order of `nuPoly Y`.
Meaningful when `nuPoly Y ≠ 0` (positive denominator); junk otherwise, never read unguarded.
Source: [[decision-problems-v2]] Remark 3.9 (advice stance: "act-conditional belief and value
by their tremble limits"); `calibration.md` D4
Kind: D
Fidelity: variant: limit taken algebraically -/
noncomputable def limitVal (Y : Finset Ω) : K :=
  (payPoly C B Y).coeff (nuPoly C B Y).natTrailingDegree /
    (nuPoly C B Y).coeff (nuPoly C B Y).natTrailingDegree

/-- **D4, advice-stance EDT**: at every queried `d` with tremble-realizable `O_d` at which some
`a ∧ O_d` is tremble-realizable, `supp C(d)` lies in the argmax, over the acts `a` with `a ∧ O_d`
tremble-realizable, of the tremble-limit act value `limitVal (a ∧ O_d)`. Unlike D1, the domain is
realizability, not positive limit probability (an act of limit probability `0` still has a limit
value). The escape clause `(∃ b, nuPoly (b ∧ O_d) ≠ 0) →` mirrors Definition 18's "no constraint
where `A_d^+ = ∅`" (repair round 1).
Source: [[decision-problems-v2]] Remark 3.9 (advice stance); `calibration.md` Devices (D4)
Kind: D
Fidelity: variant: limit taken algebraically; domain = tremble-realizable acts -/
def AdviceEdt : Prop :=
  ∀ d ∈ queried B, nuPoly C B (obs d) ≠ 0 → (∃ b, nuPoly C B (actEv d b ∩ obs d) ≠ 0) →
    ∀ a, 0 < (C d).w a →
    nuPoly C B (actEv d a ∩ obs d) ≠ 0 ∧
    ∀ b, nuPoly C B (actEv d b ∩ obs d) ≠ 0 →
      limitVal C B (actEv d b ∩ obs d) ≤ limitVal C B (actEv d a ∩ obs d)

/-- The fiber-summed forced payoff mass `∑_{q ∈ F_d} R_q · G_q(a)` of a node-level policy, for an
action `a` of `d` (transported to each node's action type along `pt q = d`).
Source: [[decision-problems-v2]] §8 Theorem 1 (`∑_{q : d_q = d} R_q G_q(C, a)`); `calibration.md`
D3
Kind: D -/
def fiberForced (p : NodePolicy B) (d : ι) (a : acts d) : K :=
  ∑ q, if h : pt B q = d then forcedBelow B p q (cast (congrArg acts h.symm) a) else 0

/-- **D3, occurrence-trembled EDT** (procedure-side tremble conditioning = Theorem 1's evaluator
under `C^ε`): for all small `ε`, at every queried `d`, `supp C(d) ⊆ argmax_a ∑_{q ∈ F_d}
forcedBelow (C^ε) q a`. `dp-local-opt` owns the functional; this is its name here.
Source: `calibration.md` Devices (D3)
Kind: D -/
def OccTrembleEdtConsistent : Prop :=
  ∃ ε₀ > (0 : K), ∀ ε, ∀ (h0 : 0 < ε) (h1 : ε ≤ 1), ε < ε₀ →
    ∀ d ∈ queried B, ∀ a, 0 < (C d).w a → ∀ b,
      fiberForced B (NodePolicy.ofProc (tremble C ε h0.le h1) B) d b ≤
        fiberForced B (NodePolicy.ofProc (tremble C ε h0.le h1) B) d a

/-- **D3⁰**: D3 at `ε = 0`, Theorem 1's local-optimality condition proper.
Source: `calibration.md` Devices (D3⁰)
Kind: D -/
def OccEdtConsistent : Prop :=
  ∀ d ∈ queried B, ∀ a, 0 < (C d).w a → ∀ b,
    fiberForced B (NodePolicy.ofProc C B) d b ≤ fiberForced B (NodePolicy.ofProc C B) d a

/-- The D2 condition at one `ε` for one procedure `C'` (the body of D2, factored out for the
test-sequence form), with Definition 18's escape clause at points where no action event is
realized within `O_d` under `C'^ε` (the `nuPoly ≠ 0` guard is then redundant and kept for
readability, as in `EventTrembleEdtConsistent`).
Source: `dynamic.md` DY-3; [[decision-problems-v2]] §4 Definition 18 (the escape clause)
Kind: D
Fidelity: exact (domain convention as `EventTrembleEdtConsistent`) -/
def D2At (C' : Proc ι acts K) (ε : K) (h0 : 0 < ε) (h1 : ε ≤ 1) : Prop :=
  ∀ d ∈ queried B, nuPoly C' B (obs d) ≠ 0 →
    (∃ b, 0 < nu (tremble C' ε h0.le h1) B (actEv d b ∩ obs d)) → ∀ a, 0 < (C' d).w a →
    0 < nu (tremble C' ε h0.le h1) B (actEv d a ∩ obs d) ∧
    ∀ b, 0 < nu (tremble C' ε h0.le h1) B (actEv d b ∩ obs d) →
      condExp (tremble C' ε h0.le h1) B (actEv d b ∩ obs d) ≤
        condExp (tremble C' ε h0.le h1) B (actEv d a ∩ obs d)

/-- **DY-3, the test-sequence form**: there are `ε_n → 0` in `(0, 1]` and procedures `C_n → C`
(pointwise in every weight) with the D2 condition at `ε_n` for `C_n` for every `n`. Convergence
is stated elementarily (no topology).
Source: `cf-workflow/phase2-notes/repair/dynamic.md` DY-3
Kind: D
Fidelity: exact -/
def TestSeqTrembleEdtConsistent : Prop :=
  ∃ (ε : ℕ → K) (Cn : ℕ → Proc ι acts K) (hε : ∀ n, 0 < ε n ∧ ε n ≤ 1),
    (∀ δ > (0 : K), ∃ N, ∀ n ≥ N, ε n < δ) ∧
    (∀ d a, ∀ δ > (0 : K), ∃ N, ∀ n ≥ N, |(Cn n d).w a - (C d).w a| < δ) ∧
    ∀ n, D2At obs actEv B (Cn n) (ε n) (hε n).1 (hε n).2

/-- **D2 ⟹ the test-sequence form** (constant sequence `C_n := C`, `ε_n := ε₀/(n+2)`), over an
Archimedean field.
Source: `dynamic.md` DY-3 ("the sequence form is the form a convergence statement has")
Kind: L
Fidelity: exact
Hyps: (a) D2 -/
theorem testSeq_of_eventTremble [Archimedean K] (h : EventTrembleEdtConsistent obs actEv C B) :
    TestSeqTrembleEdtConsistent obs actEv C B := by
  obtain ⟨ε₀, hε₀, hD2⟩ := h
  let ε : ℕ → K := fun n => min ε₀ 1 / (n + 2)
  have hεpos : ∀ n, 0 < ε n := fun n => by
    apply div_pos (lt_min hε₀ one_pos)
    positivity
  have hεle : ∀ n, ε n ≤ 1 := fun n => by
    show min ε₀ 1 / (n + 2) ≤ 1
    rw [div_le_one (by positivity)]
    calc min ε₀ 1 ≤ 1 := min_le_right _ _
      _ ≤ (n : K) + 2 := by linarith [(Nat.cast_nonneg n : (0 : K) ≤ n)]
  have hεlt : ∀ n, ε n < ε₀ := fun n => by
    show min ε₀ 1 / (n + 2) < ε₀
    rw [div_lt_iff₀ (by positivity)]
    have h1 : min ε₀ 1 ≤ ε₀ := min_le_left _ _
    have h2 : (2 : K) ≤ n + 2 := by linarith [(Nat.cast_nonneg n : (0 : K) ≤ n)]
    nlinarith
  refine ⟨ε, fun _ => C, fun n => ⟨hεpos n, hεle n⟩, ?_, ?_, ?_⟩
  · intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_gt (min ε₀ 1 / δ)
    refine ⟨N, fun n hn => ?_⟩
    show min ε₀ 1 / (n + 2) < δ
    rw [div_lt_iff₀ (by positivity)]
    have : min ε₀ 1 < δ * N := by
      rw [div_lt_iff₀ hδ] at hN; linarith
    have hnN : (N : K) ≤ n := by exact_mod_cast hn
    nlinarith
  · intro d a δ hδ
    exact ⟨0, fun n _ => by simp [hδ]⟩
  · intro n
    exact hD2 (ε n) (hεpos n) (hεle n) (hεlt n)

end devices

end Cleanroom.Decision.DpCalibration
