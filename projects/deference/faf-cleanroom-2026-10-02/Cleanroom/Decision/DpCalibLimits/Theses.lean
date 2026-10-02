import Cleanroom.Decision.DpCalibLimits.TwoRoute

/-!
# T11 — The Weak Thesis typed as a grade on the miniature; Levi's vacuity

[[dp-calib-limits-mandate]] T11 (dp-sl-064, S15, L3-2′/3′/6′).

* **The Weak Thesis is a grade, on the miniature under Definition 6** (`WeakThesisAt`, T11(a)):
  every LF-masked witness state has `P_s(a) = m ∈ (0,1)` (`miniature_masked_weak`); the strict
  state of `tremble (procQ 0) ε` (= `procQ (ε/2)`) has `P(a) = ε/2` and that of
  `tremble (procQ 1) ε` has `1 − ε/2` — `WeakThesisAt` holds for `ε ∈ (0,1)`
  (`miniature_tremble_weak`); the strict (= limit, `O = ⊤`) states at the pure labels violate
  it (`miniature_pure_not_weak`).
* **Levi's vacuity as a theorem-let** (`levi_vacuity`, T11(c)): recording + positivity +
  deterministic + strict ⟹ `A_d^+ = {C(d)}` and `T_EDT` approves — one line over
  `tEdtAt_of_deterministic_recorded`; witnessed on the *recorded* `coinQuery`
  (`coinQuery_deterministic_instance`), not the miniature (`miniature_not_recordsFor`, L3-3′).
* **The Strong Thesis is inexpressible** (T11(d)): a fact about the type `State` — `P` is
  total, every act event gets a number — recorded in `WeakThesisAt`'s docstring and in the
  findings; no theorem.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-- **The canonical LF-masked witness state on the miniature has `P_s(a) = m ∈ (0,1)`** and
satisfies the Weak Thesis: the calibrated state of the self-model `procQ m` has `P(a) = m`,
`P(b) = 1 − m`. This is one witness state per `m`; the universal over *every* masked state at
`d` is `miniature_masked_weak_all` (repair round 1, fidelity B2).
Source: L3-6′; S15 ("the Weak Thesis is a grade"); mandate T11(b)
Kind: N+
Fidelity: exact (the N+ of `miniature_masked_weak_all`)
Hyps: (a) `0 < m < 1` -/
theorem miniature_masked_weak (m : ℚ) (h0 : 0 < m) (h1 : m < 1) :
    (miniState m h0.le h1.le).pr (miniActEv () .a) = m ∧
    WeakThesisAt miniActEv (fun _ => miniState m h0.le h1.le) () := by
  refine ⟨by rw [miniState_pr_live]; rfl, fun a => ?_⟩
  cases a <;> rw [miniState_pr_live] <;> simp [procQ] <;> constructor <;> linarith

/-- **Every LF-masked state on the miniature has `P_s(a) = m ∈ (0,1)` and satisfies the Weak
Thesis**, for every label `q` (L3-6′'s sentence, "masked states have `P_{s_d}(a) = m ∈ (0,1)`
for every admissible self-model"): `O = ⊤` kills the vacuity disjunct (`ν(⊤) = 1` under the
uniform self-model), so Definition 9 holds through some full-support `m` with the strict
clauses under `C[d ↦ m]`, and clause 1 at the act events pins `P_s(a) = m(a)`, `P_s(b) = m(b)`,
both in `(0,1)`.
Source: L3-6′; S15 ("the Weak Thesis is a grade"); mandate T11(b); audit r1 fidelity B2
Kind: P
Fidelity: exact
Hyps: (a) `MaskedOCAt s` at `d` (Definition 9, the record: LF, vacuity) -/
theorem miniature_masked_weak_all (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (s : Unit → State MiniW ℚ)
    (hs : MaskedOCAt s miniObs (procQ q h0 h1) miniature ()) :
    ∃ m : ℚ, 0 < m ∧ m < 1 ∧ (s ()).pr (miniActEv () .a) = m ∧
      WeakThesisAt miniActEv s () := by
  rcases hs with ⟨C', ⟨m, hm, rfl⟩, -, hcl⟩ | ⟨-, hnull⟩
  · have hP : ∀ a, (s ()).pr (miniActEv () a) = m.w a := fun a => by
      have := hcl.1 (miniActEv () a)
      simp only [miniObs, nu_univ, mul_one, Finset.inter_univ] at this
      rw [this, miniature_nu_live, Proc.deviate_same]
    have hsum := m.sum_one
    rw [Act2.sum_univ] at hsum
    refine ⟨m.w .a, hm .a, by linarith [hm .b], hP .a, fun a => ?_⟩
    rw [hP a]
    cases a
    · exact ⟨hm .a, by linarith [hm .b]⟩
    · exact ⟨hm .b, by linarith [hm .a]⟩
  · exfalso
    have := hnull _ ⟨FinDistr.uniform, fun a => FinDistr.uniform_w_pos a, rfl⟩
    simp [miniObs, nu_univ] at this

/-- `tremble (procQ 0) ε = procQ (ε/2)`. Source: mandate T11(b). Kind: L -/
theorem tremble_procQ_zero (ε : ℚ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    tremble (procQ 0 le_rfl zero_le_one) ε h0 h1 = procQ (ε / 2) (by linarith) (by linarith) := by
  funext d; apply FinDistr.ext'; intro a
  cases a <;> simp [tremble_w, procQ, act2_card_rat] <;> ring

/-- `tremble (procQ 1) ε = procQ (1 − ε/2)`. Source: mandate T11(b). Kind: L -/
theorem tremble_procQ_one (ε : ℚ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    tremble (procQ 1 zero_le_one le_rfl) ε h0 h1 = procQ (1 - ε / 2) (by linarith) (by linarith) := by
  funext d; apply FinDistr.ext'; intro a
  cases a <;> simp [tremble_w, procQ, act2_card_rat] <;> ring

/-- **The strict states of the trembled pure labels satisfy the Weak Thesis** for `ε ∈ (0,1)`:
`P(a) = ε/2` for `tremble (procQ 0) ε` and `1 − ε/2` for `tremble (procQ 1) ε`, both in `(0,1)`.
Source: L3-6′; S15; mandate T11(b)
Kind: N+
Fidelity: exact
Hyps: (a) `0 < ε < 1` -/
theorem miniature_tremble_weak (ε : ℚ) (h0 : 0 < ε) (h1 : ε < 1) :
    WeakThesisAt miniActEv (fun _ => miniState (ε / 2) (by linarith) (by linarith)) () ∧
    WeakThesisAt miniActEv (fun _ => miniState (1 - ε / 2) (by linarith) (by linarith)) () := by
  constructor <;> intro a <;> cases a <;> rw [miniState_pr_live] <;> simp [procQ] <;>
    constructor <;> linarith

/-- **The strict (= limit, `O = ⊤`) states at the pure labels violate the Weak Thesis**:
`P(a) = 0` at `procQ 0`, `P(b) = 0` at `procQ 1`.
Source: L3-6′; S15; mandate T11(b)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem miniature_pure_not_weak :
    ¬ WeakThesisAt miniActEv (fun _ => miniState 0 le_rfl zero_le_one) () ∧
    ¬ WeakThesisAt miniActEv (fun _ => miniState 1 zero_le_one le_rfl) () := by
  constructor
  · intro h
    have := (h .a).1
    rw [miniState_pr_live] at this
    simp [procQ] at this
  · intro h
    have := (h .b).1
    rw [miniState_pr_live] at this
    simp [procQ] at this

section levi

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-- **Levi's vacuity as a theorem-let**: at a recorded positive point, a deterministic strictly
calibrated procedure has `A_d^+ = {C(d)}` and is `T_EDT`-approved there — advocacy is vacuous
under self-knowledge. One line over `dp-calibration`'s `tEdtAt_of_deterministic_recorded`; the
row's value is the name and the scope: it must be witnessed on a *recorded* tree
(`coinQuery_deterministic_instance`), not on the miniature (`miniature_not_recordsFor`).
Source: L3-3′ (correction: Levi's vacuity needs recording); L3-2′; S15
Kind: L (one citation of `tEdtAt_of_deterministic_recorded`; regraded in repair round 2, fidelity N5)
Fidelity: exact (per point, with the positivity guard)
Hyps: (a) `C d = δ_{a₀}`, (a) `RecordsFor`, (a) `0 < ν(O_d)`, (a) `StrictOCAt` -/
theorem levi_vacuity (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
    (C : Proc ι acts K) (B : Tree Ω ι acts K) (s : ι → State Ω K) {d : ι} (a₀ : acts d)
    (hC : C d = FinDistr.pure a₀) (hrec : RecordsFor obs actEv C B d)
    (hpos : 0 < nu C B (obs d)) (hs : StrictOCAt s obs C B d) :
    APlus s actEv d = {a₀} ∧ TEdtAt s actEv C d :=
  tEdtAt_of_deterministic_recorded s actEv obs C B a₀ hC hrec hpos hs

end levi

/-- Levi's vacuity witnessed on the recorded `coinQuery` (cited): `A_d^+ = {a}` and `T_EDT`
approves `procQ 1`; and the miniature is recorded by no procedure, so the theorem-let does not
apply there. Source: L3-3′; `dp-calibration`. Kind: N+ -/
theorem levi_vacuity_scope :
    (APlus (fun _ => cqStrictState 1 zero_le_one le_rfl) cqActEv () = {Act2.a} ∧
      TEdtAt (fun _ => cqStrictState 1 zero_le_one le_rfl) cqActEv (procQ 1 zero_le_one le_rfl) ()) ∧
    ∀ C : Proc Unit (fun _ => Act2) ℚ, ¬ RecordsFor miniObs miniActEv C miniature () :=
  ⟨coinQuery_deterministic_instance, miniature_not_recordsFor⟩

end Cleanroom.Decision.DpCalibLimits
