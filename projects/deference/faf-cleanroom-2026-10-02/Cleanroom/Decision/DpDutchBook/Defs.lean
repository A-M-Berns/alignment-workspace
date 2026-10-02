import Cleanroom.Decision.DpCalibration.Theories

/-!
# `dp-dutch-book` — definitions of record (mandate §3.2–3.3)

* `SupposedVal d := acts d → K` — **the counterfactual slot reduced to its act values.** v2's
  Definition 2 carries a full supposed state `cf_s(a)`; every theorem of this package reads only
  `V^a_{s_d}(a) =: c a` (P12's `c`), so the slot is modelled as that function. Disclosed here and
  on every declaration that consumes it (`Fidelity: variant: cf reduced to its act values`).
* `r3Val C B d m a` — D4's tremble-pinned act value at the point-deviation `C[d ↦ m]`
  (`dp-calibration`'s `limitVal`, the R3 referent of the SL ledgers).
* `brSet C B d m` — Definition 18's best-response face against the label `m`: the mixed actions
  whose support lies in the argmax of `r3Val m`.
* `MsrAtD4 C B d` — **D4 at one point**: `C(d) ∈ brSet (C d)`. The definition of record `MSRAt`
  is `dp-calib-limits`'s; it proves `MSRAt ↔ AdviceEdt` modulo escape clauses. This package makes
  no claim about `MSRAt`; `msrAtD4_iff_adviceEdt_clause` ties `MsrAtD4` to the `d`-clause of
  `dp-calibration`'s `AdviceEdt` when every act is tremble-realizable within `O_d`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpDutchBook

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-- **The counterfactual slot, reduced to act values**: `c : acts d → K` with `c a` read as
v2's supposed value `V^a_{s_d}(a)` of the act `a` under its own supposition.
Source: `sl-workflow/notes/repair/P12.md` Setting (`c := V^a_{s_d}(a)`); [[decision-problems-v2]]
Definition 2 (`cf_s`)
Kind: D
Fidelity: variant: cf reduced to its act values; v2 Definition 2's full supposed state is not
needed by any theorem here -/
abbrev SupposedVal (d : ι) (K : Type) : Type := acts d → K

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)

/-- **D4's tremble-pinned act value at the deviation `C[d ↦ m]`** (the R3 referent):
`limitVal (C[d ↦ m]) B (a ∧ O_d)`.
Source: `repair/C2.md` line 42 (MSR: "`v_d` read as the tremble-pinned evidential act value at
the strictly calibrated state (R3)"); `calibration.md` D4
Kind: D
Fidelity: variant: limit taken algebraically (`dp-calibration`'s `limitVal`) -/
noncomputable def r3Val (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)
    (m : FinDistr K (acts d)) (a : acts d) : K :=
  limitVal (C.deviate d m) B (actEv d a ∩ obs d)

/-- **The best-response face against the label `m`** (Definition 18's support-in-argmax): the
mixed actions `m'` whose support lies in `argmax_a r3Val m a`.
Source: `repair/C2.md` line 72 (C2-7: "`m ↦ {m' : supp m' ⊆ argmax_a v(a; m)}`");
[[decision-problems-v2]] §4 Definition 18
Kind: D
Fidelity: exact (argmax over all of `A_d`, the R3 extension valuing every act) -/
def brSet (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (m : FinDistr K (acts d)) :
    Set (FinDistr K (acts d)) :=
  {m' | ∀ a, 0 < m'.w a → ∀ b, r3Val obs actEv C B d m b ≤ r3Val obs actEv C B d m a}

/-- **MSR at one point, D4 form**: `C(d)` is a best response to itself, `C(d) ∈ brSet (C d)`.
`dp-calib-limits` owns the definition of record `MSRAt` and proves `MSRAt ↔ AdviceEdt` modulo
escape clauses; this package makes no claim about `MSRAt`.
Source: `repair/C2.md` line 42 (MSR); `sl-defensible-claims.md` S10
Kind: D
Fidelity: variant: one point, D4 values, argmax over all of `A_d` (no realizability guard on the
compared acts — see `msrAtD4_iff_adviceEdt_clause`) -/
def MsrAtD4 (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) : Prop :=
  C d ∈ brSet obs actEv C B d (C d)

/-- `C[d ↦ C d] = C`. Source: none: infrastructure. Kind: L -/
theorem Proc.deviate_self (C : Proc ι acts K) (d : ι) : C.deviate d (C d) = C :=
  Function.update_eq_self d C

/-- `C[d ↦ m][d ↦ m'] = C[d ↦ m']`. Source: none: infrastructure. Kind: L -/
theorem Proc.deviate_deviate (C : Proc ι acts K) (d : ι) (m m' : FinDistr K (acts d)) :
    (C.deviate d m).deviate d m' = C.deviate d m' := by
  unfold Proc.deviate; exact Function.update_idem (a := d) m m' C

/-- `r3Val` at the label of a deviation is `limitVal` of that deviation.
Source: none: infrastructure. Kind: L -/
theorem r3Val_deviate (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)
    (m m' : FinDistr K (acts d)) (a : acts d) :
    r3Val obs actEv (C.deviate d m) B d m' a = r3Val obs actEv C B d m' a := by
  unfold r3Val; rw [Proc.deviate_deviate]

/-- `MsrAtD4` at a deviation, unfolded: `m ∈ brSet C B d m` (the fixed-point form Kakutani
delivers).
Source: none: infrastructure. Kind: L -/
theorem msrAtD4_deviate_iff (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)
    (m : FinDistr K (acts d)) :
    MsrAtD4 obs actEv (C.deviate d m) B d ↔ m ∈ brSet obs actEv C B d m := by
  unfold MsrAtD4 brSet
  simp only [Set.mem_setOf_eq, Proc.deviate_same, r3Val_deviate]

/-- **`MsrAtD4` is the `d`-clause of `AdviceEdt` when every act is tremble-realizable within
`O_d`**: under `∀ b, nuPoly C B (b ∧ O_d) ≠ 0`, `C(d) ∈ brSet (C d)` holds iff every supported
`a` has `nuPoly (a ∧ O_d) ≠ 0` (automatic) and dominates every realizable `b` in `limitVal`
(all `b` are realizable). Without the realizability hypothesis the two differ: `brSet` compares
against the junk `limitVal` of an unrealizable act, `AdviceEdt` does not.
Source: `repair/C2.md` line 42 (MSR = D4 with R3 values); `calibration.md` D4
Kind: L
Fidelity: exact under the stated realizability hypothesis
Hyps: (a) every act event realizable within `O_d` under trembles (a structural fact on the trees
of this package, derived there) -/
theorem msrAtD4_iff_adviceEdt_clause (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)
    (hall : ∀ b, nuPoly C B (actEv d b ∩ obs d) ≠ 0) :
    MsrAtD4 obs actEv C B d ↔
      (∀ a, 0 < (C d).w a → nuPoly C B (actEv d a ∩ obs d) ≠ 0 ∧
        ∀ b, nuPoly C B (actEv d b ∩ obs d) ≠ 0 →
          limitVal C B (actEv d b ∩ obs d) ≤ limitVal C B (actEv d a ∩ obs d)) := by
  unfold MsrAtD4 brSet r3Val
  simp only [Set.mem_setOf_eq, Proc.deviate_self]
  constructor
  · intro h a ha
    exact ⟨hall a, fun b _ => h a ha b⟩
  · intro h a ha b
    exact (h a ha).2 b (hall b)

/-- The `d`-clause of `AdviceEdt` follows from `AdviceEdt` at a queried, realizable point.
Source: none: infrastructure. Kind: L -/
theorem adviceEdt_clause_of_adviceEdt (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)
    (h : AdviceEdt obs actEv C B) (hd : d ∈ queried B) (hO : nuPoly C B (obs d) ≠ 0)
    (hall : ∀ b, nuPoly C B (actEv d b ∩ obs d) ≠ 0) :
    MsrAtD4 obs actEv C B d := by
  rw [msrAtD4_iff_adviceEdt_clause obs actEv C B d hall]
  exact h d hd hO ⟨Classical.arbitrary _, hall _⟩

end Cleanroom.Decision.DpDutchBook
