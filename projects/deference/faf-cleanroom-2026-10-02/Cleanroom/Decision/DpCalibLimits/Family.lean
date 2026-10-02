import Cleanroom.Decision.DpCalibLimits.Seq
import Cleanroom.Decision.DpCalibLimits.Nonstandard

/-!
# T4 — The device family `FF ⊆ TS ⊆ MSR ⊆ MSR¹⁷` and εFP

[[dp-calib-limits-mandate]] T4 (dp-sl-005, S10, C2-9′/20′, SL-21, SE-18′(b)–(c)).

* **MSR vs D4** (`msrAt_imp_adviceEdt_body`, `msr_imp_adviceEdt`, `msr_iff_adviceEdt`):
  Definition 18′'s `MSRAt` is D4's body without the guards; the two coincide at every
  queried point whose observation and some act event are tremble-realizable.
* **FF ⊆ TS**: `dp-calibration`'s `testSeq_of_eventTremble` (`ff_subset_ts`).
* **TS ⊆ MSR under realized acts** (`msrAt_of_ts_of_realized`): along a test sequence the
  trembled act values converge to the strict values of `C` (continuity of a quotient of
  polynomials in the weights, `Seq.lean`), weak inequalities pass to the limit, and the strict
  values are the `limitVal`s (`limitVal_eq_of_pos`). **Without realized acts the inclusion
  fails**: `TsMsr.lean`.
* **MSR ⊆ MSR¹⁷ under recording** (`msr17At_of_msrAt_recorded`): at a recorded positive
  point with a strictly calibrated state, `A_d^+ = supp C(d)` and the state's act values are
  the `limitVal`s, so D4's argmax contains Definition 17's. Strictness: on the miniature the
  pure label `a` is `T_EDT`-approved at its strict state but not MSR
  (`miniature_msr17_not_msr`). On the routing root MSR and `T_EDT`-at-the-strict-state agree
  (`routingRoot_msrAt_iff`), so that tree does not separate them.
* **εFP** (`epsFP_tremble_iff_d2At`, `ts_of_epsFP_limit`): an act sits strictly above the
  `ε`-floor of `C'^ε` iff it is in `supp C'`, so εFP for `C'^ε` is the D2 condition for `C'`
  at `ε`; and the limit of a sequence of `ε_n`-floored fixed points is test-sequence
  consistent (de-tremble each term: `detremble`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

section family

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]
  (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω) (C : Proc ι acts K)
  (B : Tree Ω ι acts K)

/-! ## (a) MSR and D4 -/

/-- `MSRAt` is D4's body at `d` without the guards.
Source: SL-21 Definition 18′ vs `calibration.md` D4; mandate §3.5
Kind: L -/
theorem msrAt_imp_adviceEdt_body (d : ι) (h : MSRAt obs actEv C B d) :
    nuPoly C B (obs d) ≠ 0 → (∃ b, nuPoly C B (actEv d b ∩ obs d) ≠ 0) →
      ∀ a, 0 < (C d).w a → nuPoly C B (actEv d a ∩ obs d) ≠ 0 ∧
        ∀ b, nuPoly C B (actEv d b ∩ obs d) ≠ 0 →
          limitVal C B (actEv d b ∩ obs d) ≤ limitVal C B (actEv d a ∩ obs d) :=
  fun _ _ a ha => h a ha

/-- **MSR implies D4** on every tree. Source: SL-21; mandate T4(a). Kind: L -/
theorem msr_imp_adviceEdt (h : MSR obs actEv C B) : AdviceEdt obs actEv C B :=
  fun d hd => msrAt_imp_adviceEdt_body obs actEv C B d (h d hd)

/-- **MSR = D4 where every queried observation and some act event are tremble-realizable**:
the only difference is D4's escape clauses.
Source: SL-21 Definition 18′; `calibration.md` D4; mandate §3.5 ("state exactly where they
differ")
Kind: L
Fidelity: exact -/
theorem msr_iff_adviceEdt
    (hg : ∀ d ∈ queried B, nuPoly C B (obs d) ≠ 0 ∧ ∃ b, nuPoly C B (actEv d b ∩ obs d) ≠ 0) :
    MSR obs actEv C B ↔ AdviceEdt obs actEv C B := by
  refine ⟨msr_imp_adviceEdt obs actEv C B, fun h d hd a ha => ?_⟩
  exact h d hd (hg d hd).1 (hg d hd).2 a ha

/-! ## (b) FF ⊆ TS -/

/-- **FF ⊆ TS**: `dp-calibration`'s `testSeq_of_eventTremble` (constant sequence).
Source: S10 / C2-9′ ("FF ⊆ TS"); `dynamic.md` DY-3
Kind: L -/
theorem ff_subset_ts [Archimedean K] (h : FF obs actEv C B) : TS obs actEv C B :=
  testSeq_of_eventTremble obs actEv C B h

/-! ## (c) TS ⊆ MSR under realized acts -/

/-- **TS ⊆ MSR at a point where every act event is realized under `C`**: along the test
sequence the trembled procedures converge to `C`, so their act values converge to the strict
values of `C` (`condExp_tendsTo`), which are positive-mass conditionals, hence the `limitVal`s
(`limitVal_eq_of_pos`); the D2 comparisons hold along the sequence and pass to the limit.
Source: S10 / C2-9′ ("TS ⊆ MSR") under SE-18′(b)'s added positivity ("under the added
hypothesis that `ν_{C₀}(a ∧ O_d) > 0` for every `a`"); P04 Open 11
Kind: C
Fidelity: weaker: the sources' unguarded inclusion is false (`TsMsr.lean`); this is the
guarded form SE-18′(b) states
Hyps: (a) `TS`, (a) `∀ a, 0 < ν_C(a ∧ O_d)` -/
theorem msrAt_of_ts_of_realized (hTS : TS obs actEv C B) (d : ι) (hd : d ∈ queried B)
    (hreal : ∀ a, 0 < nu C B (actEv d a ∩ obs d)) : MSRAt obs actEv C B d := by
  obtain ⟨ε, Cn, hε, hε0, hCn, hD2⟩ := hTS
  have hε0' : SeqTendsTo ε 0 := fun δ hδ => by
    obtain ⟨N, hN⟩ := hε0 δ hδ
    exact ⟨N, fun n hn => by rw [sub_zero, abs_of_pos (hε n).1]; exact hN n hn⟩
  have hCn' : ProcTendsTo Cn C := fun d a => hCn d a
  have hDconv : ProcTendsTo (fun n => tremble (Cn n) (ε n) (hε n).1.le (hε n).2) C :=
    tremble_tendsTo Cn ε (fun n => ⟨(hε n).1.le, (hε n).2⟩) hε0' hCn'
  intro a ha
  have hOpos : 0 < nu C B (obs d) :=
    lt_of_lt_of_le (hreal a) (nu_mono C B Finset.inter_subset_right)
  have hOne : nuPoly C B (obs d) ≠ 0 := (natTrailingDegree_nuPoly_eq_zero C B _ hOpos).2
  have hOne' : ∀ n, nuPoly (Cn n) B (obs d) ≠ 0 := fun n => by
    rw [nuPoly_ne_zero_iff] at hOne ⊢; exact hOne
  refine ⟨(natTrailingDegree_nuPoly_eq_zero C B _ (hreal a)).2, fun b _ => ?_⟩
  rw [limitVal_eq_of_pos C B _ (hreal a), limitVal_eq_of_pos C B _ (hreal b)]
  obtain ⟨N₁, hN₁⟩ := SeqTendsTo.eventually_pos (hCn' d a) ha
  obtain ⟨N₂, hN₂⟩ := (nu_tendsTo hDconv B (actEv d a ∩ obs d)).eventually_pos (hreal a)
  obtain ⟨N₃, hN₃⟩ := (nu_tendsTo hDconv B (actEv d b ∩ obs d)).eventually_pos (hreal b)
  apply SeqTendsTo.le_of_eventually_le (condExp_tendsTo hDconv B _ (hreal b))
    (condExp_tendsTo hDconv B _ (hreal a))
  refine ⟨max N₁ (max N₂ N₃), fun n hn => ?_⟩
  have h1 := hN₁ n (le_of_max_le_left hn)
  have h2 := hN₂ n (le_of_max_le_left (le_of_max_le_right hn))
  have h3 := hN₃ n (le_of_max_le_right (le_of_max_le_right hn))
  exact ((hD2 n) d hd (hOne' n) ⟨a, h2⟩ a h1).2 b h3

/-! ## (d) MSR ⊆ MSR¹⁷ under recording -/

/-- **MSR ⊆ MSR¹⁷ at a recorded positive point**: with `s_d` strictly calibrated, `RecordsFor`
gives `ν(a ∧ O_d) = C(d)(a) ν(O_d)`, so `A_d^+ = supp C(d)`; the state's act values are the
strict conditionals, which are the `limitVal`s; D4's argmax over realizable acts therefore
contains Definition 17's argmax over `A_d^+`, and `T_EDT` approves `C` at `d`.
Source: SL-21 ("Read on Definition 17's domain `A_d^+` instead, the condition approves every
deterministic label vacuously"); C2-9′ ("MSR ⊆ MSR¹⁷"); mandate T4(d)
Kind: C
Fidelity: exact (per point, at a strictly calibrated state)
Hyps: (a) `StrictOCAt`, (a) `RecordsFor` (Definition 7), (a) `0 < ν(O_d)`, (a) `MSRAt` -/
theorem msr17At_of_msrAt_recorded (s : ι → State Ω K) (d : ι) (hs : StrictOCAt s obs C B d)
    (hrec : RecordsFor obs actEv C B d) (hpos : 0 < nu C B (obs d))
    (hmsr : MSRAt obs actEv C B d) : MSR17At actEv C s d := by
  intro _ a ha
  obtain ⟨h1, h2⟩ := hs hpos
  have hrecw := nu_actEv_inter_obs_of_recordsFor obs actEv C B hrec
  -- `P_s(a) = C(d)(a)`
  have hP : ∀ b, (s d).pr (actEv d b) = (C d).w b := fun b => by
    have := h1 (actEv d b)
    rw [hrecw b] at this
    exact mul_right_cancel₀ hpos.ne' this
  -- `V_s(b) = condExp` where `P_s(b) > 0`
  have hV : ∀ b, 0 < (s d).pr (actEv d b) →
      (s d).V (actEv d b) = condExp C B (actEv d b ∩ obs d) := fun b hb => by
    have hb' : 0 < nu C B (actEv d b ∩ obs d) := by
      rw [hrecw b, ← hP b]; exact mul_pos hb hpos
    have := h2 (actEv d b) hb hb'
    unfold condExp
    rw [eq_div_iff hb'.ne']
    exact this
  rw [mem_argmaxPlus]
  refine ⟨?_, fun b hb => ?_⟩
  · unfold APlus; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by rw [hP]; exact ha⟩
  · have hbP : 0 < (s d).pr (actEv d b) := by
      unfold APlus at hb; rw [Finset.mem_filter] at hb; exact hb.2
    have haP : 0 < (s d).pr (actEv d a) := by rw [hP]; exact ha
    have hbν : 0 < nu C B (actEv d b ∩ obs d) := by
      rw [hrecw b, ← hP b]; exact mul_pos hbP hpos
    have haν : 0 < nu C B (actEv d a ∩ obs d) := by
      rw [hrecw a, ← hP a]; exact mul_pos haP hpos
    rw [hV b hbP, hV a haP, ← limitVal_eq_of_pos C B _ hbν, ← limitVal_eq_of_pos C B _ haν]
    exact (hmsr a ha).2 b (natTrailingDegree_nuPoly_eq_zero C B _ hbν).2

end family

/-! ## Strictness of MSR ⊆ MSR¹⁷: the miniature -/

/-- **MSR¹⁷ ⊄ MSR on the miniature**: the pure label `a` is `T_EDT`-approved at its strict
state (`miniature_tEdt_pure_a`) but not MSR — D4 approves only `2/3`
(`miniature_adviceEdt_iff`). This is `⊄`, not `⊋`: the inclusion `msr17At_of_msrAt_recorded`
needs recording and the miniature is recorded by no procedure (`miniature_not_recordsFor`), so
the in-domain strictness witness is `t1_msr17_not_msr` (`WitnessesR1.lean`, the recorded `t1`).
Source: SL-21 ("the condition approves every deterministic label vacuously"); C2-9′; mandate
T4(d)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem miniature_msr17_not_msr :
    MSR17At miniActEv (procQ 1 (by norm_num) le_rfl) (fun _ => miniState 1 (by norm_num) le_rfl) () ∧
    ¬ MSRAt miniObs miniActEv (procQ 1 (by norm_num) le_rfl) miniature () := by
  refine ⟨miniature_tEdt_pure_a, fun h => ?_⟩
  have hmsr : MSR miniObs miniActEv (procQ 1 (by norm_num) le_rfl) miniature := fun d _ => by
    cases d; exact h
  have := (miniature_adviceEdt_iff 1 (by norm_num) le_rfl).mp
    (msr_imp_adviceEdt _ _ _ _ hmsr)
  norm_num at this

/-! ## The routing root does not separate MSR from `T_EDT` -/

/-- A sum over the leaves of the routing root. Source: none: infrastructure. Kind: L -/
theorem routingRoot_sum {M : Type} [AddCommMonoid M] (f : routingRoot.Leaves → M) :
    ∑ ℓ, f ℓ = f ⟨.a, ()⟩ + f ⟨.b, ()⟩ := by
  unfold routingRoot at f ⊢
  rw [sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf]

/-- **On the routing root MSR at `d` holds iff `C(d) = δ_a`**: the `b`-event within
`O = {inO}` is empty, so a supported `b` violates Definition 18′'s unconditional realizability
clause; with `C(d) = δ_a` the comparison against `b` is vacuous. `T_EDT` at the strict state
(where `q > 0`) gives the same verdict (`A_d^+ = {a}`), so the routing root shows no gap
between MSR and MSR¹⁷ — recorded per mandate T4(d) ("find whether `MSRAt` holds while
`TEdtAt` fails, and record").
Source: mandate T4(d); [[decision-problems-v2]] Remark 3.4 (the routing root)
Kind: P
Fidelity: exact -/
theorem routingRoot_msrAt_iff (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    MSRAt routeObs routeActEv (procQ q h0 h1) routingRoot () ↔ q = 1 := by
  have hb : nuPoly (procQ q h0 h1) routingRoot (routeActEv () .b ∩ routeObs ()) = 0 := by
    rw [nuPoly_eq_sum, routingRoot_sum]
    simp [routingRoot, routeActEv, routeObs]
  constructor
  · intro h
    by_contra hq
    have hlt : 0 < (procQ q h0 h1 ()).w .b := by
      simp only [procQ, FinDistr.act2_b]
      exact sub_pos.mpr (lt_of_le_of_ne h1 hq)
    exact (h .b hlt).1 hb
  · intro hq a ha
    subst hq
    cases a
    · refine ⟨?_, fun b hb' => ?_⟩
      · rw [nuPoly_ne_zero_iff]
        exact ⟨⟨.a, ()⟩, by simp [routingRoot, routeActEv, routeObs], by simp [routingRoot]⟩
      · cases b
        · exact le_rfl
        · exact absurd hb hb'
    · simp [procQ] at ha

/-! ## (e) εFP -/

section epsFP

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]
  (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω) (B : Tree Ω ι acts K)

/-- **The floor/support dictionary**: an act sits strictly above the `ε`-floor of `C'^ε` iff
it is in `supp C'` (for `ε < 1`). Source: P07 I1′ rider ("floor ↔ support"). Kind: L -/
theorem tremble_gt_floor_iff (C' : Proc ι acts K) (ε : K) (h0 : 0 ≤ ε) (h1 : ε < 1) (d : ι)
    (a : acts d) :
    ε / (Fintype.card (acts d) : K) < (tremble C' ε h0 h1.le d).w a ↔ 0 < (C' d).w a := by
  rw [tremble_w, div_eq_mul_inv]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have : (C' d).w a = 0 := le_antisymm hc ((C' d).nonneg a)
    rw [this, mul_zero, zero_add] at h
    exact lt_irrefl _ h
  · intro h
    have : 0 < (1 - ε) * (C' d).w a := mul_pos (by linarith) h
    linarith

/-- **εFP for `C'^ε` is the D2 condition for `C'` at `ε`** (`0 < ε < 1`): the floor is
automatic, "above the floor" is "in the support", and the escape clauses coincide.
Source: P07 I1′ rider ("SE-18′'s ε-floored simplex is the image of the uniform tremble with
floor ↔ support, so εFP and TS are one parametrization"); C2-9′
Kind: L
Fidelity: exact -/
theorem epsFP_tremble_iff_d2At (C' : Proc ι acts K) (ε : K) (h0 : 0 < ε) (h1 : ε < 1) :
    EpsFP obs actEv (tremble C' ε h0.le h1.le) B ε ↔ D2At obs actEv B C' ε h0 h1.le := by
  constructor
  · rintro ⟨-, h⟩ d hd _ hex a ha
    exact h d hd hex a ((tremble_gt_floor_iff C' ε h0.le h1 d a).mpr ha)
  · intro h
    refine ⟨fun d a => ?_, fun d hd hex a hfl => ?_⟩
    · rw [tremble_w, div_eq_mul_inv]
      have := mul_nonneg (by linarith : (0 : K) ≤ 1 - ε) ((C' d).nonneg a)
      linarith
    · have hO : nuPoly C' B (obs d) ≠ 0 := by
        obtain ⟨b, hb⟩ := hex
        exact nuPoly_ne_zero_of_nu_tremble_pos C' B _ ε h0.le h1.le
          (lt_of_lt_of_le hb (nu_mono _ B Finset.inter_subset_right))
      exact h d hd hO hex a ((tremble_gt_floor_iff C' ε h0.le h1 d a).mp hfl)

/-- De-trembling: the procedure whose `ε`-tremble is `C'`, when `C'` sits above the
`ε`-floor. Source: mandate T4(e) ("de-tremble each `Cn n` to `C'n`"). Kind: D -/
noncomputable def detremble (C' : Proc ι acts K) (ε : K) (h1 : ε < 1)
    (hfl : ∀ d a, ε / (Fintype.card (acts d) : K) ≤ (C' d).w a) : Proc ι acts K :=
  fun d =>
    { w := fun a => ((C' d).w a - ε / (Fintype.card (acts d) : K)) / (1 - ε)
      nonneg := fun a => div_nonneg (by linarith [hfl d a]) (by linarith)
      sum_one := by
        have hc : (Fintype.card (acts d) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
        rw [← Finset.sum_div, Finset.sum_sub_distrib, (C' d).sum_one, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_div_cancel₀ _ hc]
        exact div_self (by linarith) }

/-- Weights of the de-trembled procedure. Source: none: infrastructure. Kind: L -/
@[simp] theorem detremble_w (C' : Proc ι acts K) (ε : K) (h1 : ε < 1)
    (hfl : ∀ d a, ε / (Fintype.card (acts d) : K) ≤ (C' d).w a) (d : ι) (a : acts d) :
    (detremble C' ε h1 hfl d).w a = ((C' d).w a - ε / (Fintype.card (acts d) : K)) / (1 - ε) :=
  rfl

/-- The tremble of the de-trembled procedure is the original.
Source: mandate T4(e). Kind: L -/
theorem tremble_detremble (C' : Proc ι acts K) (ε : K) (h0 : 0 ≤ ε) (h1 : ε < 1)
    (hfl : ∀ d a, ε / (Fintype.card (acts d) : K) ≤ (C' d).w a) :
    tremble (detremble C' ε h1 hfl) ε h0 h1.le = C' := by
  funext d
  apply FinDistr.ext'
  intro a
  rw [tremble_w, detremble_w]
  have : (1 - ε) ≠ 0 := by linarith
  field_simp
  ring

/-- **The limit of εFP fixed points is test-sequence consistent** (`lim εFP ⊆ TS`): given
`C_n ∈ EpsFP (ε_n)` with `ε_n → 0` in `(0, 1)` and `C_n → C`, de-tremble each `C_n` to `C'_n`
(so `C'_n^{ε_n} = C_n`); `C'_n → C` because `ε_n → 0`, and εFP for `C_n` is the D2 condition
for `C'_n` at `ε_n`. This is the chain's first link as an equality of parametrizations.
Source: P07 I1′ rider; SE-18′(b) ("limit points … are approved at the test-sequence-calibrated
state"); C2-9′ ("`lim εFP ⊆ TS`")
Kind: C
Fidelity: exact
Hyps: (a) the sequence data -/
theorem ts_of_epsFP_limit (C : Proc ι acts K) (ε : ℕ → K) (Cn : ℕ → Proc ι acts K)
    (hε : ∀ n, 0 < ε n ∧ ε n < 1) (hε0 : SeqTendsTo ε 0) (hCn : ProcTendsTo Cn C)
    (hFP : ∀ n, EpsFP obs actEv (Cn n) B (ε n)) : TS obs actEv C B := by
  refine ⟨ε, fun n => detremble (Cn n) (ε n) (hε n).2 (hFP n).1,
    fun n => ⟨(hε n).1, (hε n).2.le⟩, ?_, ?_, ?_⟩
  · intro δ hδ
    obtain ⟨N, hN⟩ := hε0 δ hδ
    exact ⟨N, fun n hn => by have := hN n hn; rw [sub_zero, abs_of_pos (hε n).1] at this; exact this⟩
  · intro d a
    have hconv : SeqTendsTo
        (fun n => ((Cn n d).w a - ε n * (Fintype.card (acts d) : K)⁻¹) / (1 - ε n))
        (((C d).w a - 0 * (Fintype.card (acts d) : K)⁻¹) / (1 - 0)) :=
      ((hCn d a).sub (hε0.mul (SeqTendsTo.const _))).div ((SeqTendsTo.const 1).sub hε0)
        (by norm_num)
    simp only [zero_mul, sub_zero, div_one] at hconv
    intro δ hδ
    obtain ⟨N, hN⟩ := hconv δ hδ
    exact ⟨N, fun n hn => by simpa [detremble_w, div_eq_mul_inv] using hN n hn⟩
  · intro n
    have := (hFP n)
    rw [← tremble_detremble (Cn n) (ε n) (hε n).1.le (hε n).2 (hFP n).1] at this
    exact (epsFP_tremble_iff_d2At obs actEv B _ (ε n) (hε n).1 (hε n).2).mp this

end epsFP

end Cleanroom.Decision.DpCalibLimits
