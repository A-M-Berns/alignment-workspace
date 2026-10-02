import Cleanroom.Decision.DpCalibration.Witnesses

/-!
# Remark 4.3's miniature and the selection-forcing tree: T15(b), T15(c), T16(b)

**The miniature is a nested tree**: following DY-1 ("the predictor's sample is an independent
`d`-node"), `miniature := decision () (fun s => decision () (fun l => …))` carries the point `()`
at two nodes on every path (`count () = 2`). It is therefore **not almost fair**, so the SSC
senses and `zo2_chain_at` do not apply to it, and its `occ`/`#_d` numbers differ from a one-node
reading; and it is **recorded by no procedure at `d`** (`miniature_not_recordsFor`,
`miniature_not_recordsForAll`: Definition 7 needs `count = 1`), so nothing here may be fed to a
recording theorem — CA-12′'s tie and non-forcing consequences (`Corollaries.lean`) have their
witness on the one-point tie tree (`TieTree.lean`), not on the miniature. Everything here is
stated through `nu`/`paySum` (observation calibration), on which the nesting is invisible.
(Repair round 1, audit N4; repair round 2, B1.)

* `miniState q` — the strict state of `procQ q` on the miniature (`O = ⊤`, action events the
  live draw); its act values are `V(a) = 2(1−q)` (for `q > 0`) and `V(b) = q` (for `q < 1`),
  derived from the tree (`miniState_V_a`, `miniState_V_b`).
* **Tie-freedom does existence work** (Remark 4.3): at `q = 2/3` the values tie and `(2/3, 1/3)`
  is strictly calibrated and `T_EDT`-approved (`miniature_tie_approved`).
* **CA-13′**: under Definition 17's domain `A_d^+`, the strictly-calibrated-and-approved set is
  exactly `{δ_a, δ_b, (2/3, 1/3)}`: `δ_a` and `δ_b` are approved vacuously (`A_d^+` a singleton),
  and an interior `q` is approved iff `q = 2/3` (`miniature_tEdt_pure_a`, `_pure_b`,
  `miniature_tEdt_interior_iff`). Remark 4.3's "unique" is wrong as stated.
* **Remark 5.2(i)**: the `EDT` procedure has no interior strictly-calibrated fixed point on the
  miniature — `edtProc (miniState q) = procQ q` iff `q ∈ {0, 1}` (`miniature_edt_fixed_iff`).
* **Selection forcing** `S_sel(−20,−20;10,5)`: both acts are always subjectively possible,
  `V(a) = 10(1−2q)/(1+q)`, `V(b) = (20q−15)/(2−q)`, the tie is at `q = 7/11`, and the `EDT`
  procedure has **no** strictly-calibrated fixed point at all (`sel_edt_no_fixed`).
* **D2 is empty on the miniature** (CA-14′/DY-2): no `procQ q` is event-tremble-EDT-consistent
  (`miniature_not_eventTremble`), in the faithful `∀ ε₀, ¬ ∀ ε < ε₀` form; while **D4 approves
  exactly `q = 2/3`** (`miniature_adviceEdt_iff`) — uniqueness holds for the tremble-limit
  evaluator, closing T15(b).
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

/-! ## The miniature -/

section miniature

/-- `O = ⊤` on the miniature. Source: [[decision-problems-v2]] Remark 4.3. Kind: D -/
def miniObs : Unit → Finset MiniW := fun _ => Finset.univ

/-- Action events on the miniature: the **live** draw `{(s, l) : l = a}` (the encoding CA-13′
uses; the predictor's sample is not the agent's act).
Source: `calibration.md` CA-13′ ("Miniature (live draw as the action event)")
Kind: D -/
def miniActEv (_ : Unit) (a : Act2) : Finset MiniW := Finset.univ.filter fun w => w.2 = a

/-- A sum over the leaves of the miniature as a double sum. Source: none: infrastructure. Kind: L -/
theorem miniature_sum {M : Type} [AddCommMonoid M] (f : miniature.Leaves → M) :
    ∑ ℓ, f ℓ = ∑ s : Act2, ∑ l : Act2, f ⟨s, l, ()⟩ := by
  unfold miniature at f ⊢
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- `ν(live = a) = C(d)(a)` on the miniature. Source: none: infrastructure. Kind: L -/
theorem miniature_nu_live (C : Proc Unit (fun _ => Act2) ℚ) (a : Act2) :
    nu C miniature (miniActEv () a) = (C ()).w a := by
  rw [nu_eq_sum, miniature_sum]
  have := (C ()).sum_one
  rw [Act2.sum_univ] at this
  cases a
  · simp [Act2.sum_univ, miniature, miniActEv, leafLaw_decision, world_decision]
    linear_combination (C ()).w Act2.a * this
  · simp [Act2.sum_univ, miniature, miniActEv, leafLaw_decision, world_decision]
    linear_combination (C ()).w Act2.b * this

/-- `𝔼[r · 1_{live = a}] = 2 · C(d)(b) · C(d)(a)` on the miniature. Source: none: infrastructure.
Kind: L -/
theorem miniature_paySum_live_a (C : Proc Unit (fun _ => Act2) ℚ) :
    paySum C miniature (miniActEv () .a) = 2 * (C ()).w .b * (C ()).w .a := by
  rw [paySum_eq_sum_ite, miniature_sum]
  simp [Act2.sum_univ, miniature, miniActEv, miniPay, leafLaw_decision, world_decision]
  ring

/-- `𝔼[r · 1_{live = b}] = C(d)(a) · C(d)(b)` on the miniature. Source: none: infrastructure.
Kind: L -/
theorem miniature_paySum_live_b (C : Proc Unit (fun _ => Act2) ℚ) :
    paySum C miniature (miniActEv () .b) = (C ()).w .a * (C ()).w .b := by
  rw [paySum_eq_sum_ite, miniature_sum]
  simp [Act2.sum_univ, miniature, miniActEv, miniPay, leafLaw_decision, world_decision]

/-- **The strict state of `procQ q` on the miniature** (`O = ⊤`).
Source: [[decision-problems-v2]] Remark 4.3 ("Under strict calibration the state reports the
true mixture")
Kind: D -/
noncomputable def miniState (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : State MiniW ℚ :=
  calibratedState (procQ q h0 h1) miniature Finset.univ (nu_univ_pos _ _)

/-- `P_{s}(live = a) = q`, `P_s(live = b) = 1 − q`. Source: none: infrastructure. Kind: L -/
theorem miniState_pr_live (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (a : Act2) :
    (miniState q h0 h1).pr (miniActEv () a) = (procQ q h0 h1 ()).w a := by
  rw [miniState, calibratedState_pr, Finset.inter_univ, nu_univ, div_one, miniature_nu_live]

/-- **`V_{s_d}(a) = 2(1 − q)`** for `q > 0` (derived from the tree, not input).
Source: [[decision-problems-v2]] Remark 4.3 (`V_{s_d}(a) = 2(1−q)`)
Kind: P
Fidelity: exact
Hyps: (a) `0 < q` (the guard: `a` is `P_s`-null at `q = 0`) -/
theorem miniState_V_a (q : ℚ) (h0 : 0 < q) (h1 : q ≤ 1) :
    (miniState q h0.le h1).V (miniActEv () .a) = 2 * (1 - q) := by
  rw [miniState, calibratedState_V, Finset.inter_univ, miniature_paySum_live_a,
    miniature_nu_live]
  simp only [procQ, FinDistr.act2_a, FinDistr.act2_b]
  field_simp

/-- **`V_{s_d}(b) = q`** for `q < 1`.
Source: [[decision-problems-v2]] Remark 4.3 (`V_{s_d}(b) = q`)
Kind: P
Fidelity: exact
Hyps: (a) `q < 1` -/
theorem miniState_V_b (q : ℚ) (h0 : 0 ≤ q) (h1 : q < 1) :
    (miniState q h0 h1.le).V (miniActEv () .b) = q := by
  rw [miniState, calibratedState_V, Finset.inter_univ, miniature_paySum_live_b,
    miniature_nu_live]
  simp only [procQ, FinDistr.act2_a, FinDistr.act2_b]
  have : (1 - q) ≠ 0 := by linarith
  field_simp

/-- `A_d^+` on the miniature is the support of `procQ q`. Source: none: infrastructure. Kind: L -/
theorem miniature_aPlus (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    APlus (fun _ => miniState q h0 h1) miniActEv () =
      Finset.univ.filter fun a => 0 < (procQ q h0 h1 ()).w a := by
  ext a; simp [APlus, miniState_pr_live]

/-- The miniature's strict state is strictly calibrated for `procQ q`.
Source: [[decision-problems-v2]] Remark 4.3
Kind: L -/
theorem miniature_strictOC (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    StrictOC (fun _ => miniState q h0 h1) miniObs (procQ q h0 h1) miniature :=
  fun _ _ => strictOCAt_calibratedState miniObs _ miniature _ () _ rfl

/-- **`δ_a` is approved vacuously** (`q = 1`): `A_d^+ = {a}`, so `argmax = {a} ⊇ supp`.
Source: `calibration.md` CA-13′ ("at `q ∈ {0,1}` the unplayed act is `P_s`-null and `T_EDT`
holds vacuously")
Kind: N+ -/
theorem miniature_tEdt_pure_a :
    TEdtAt (fun _ => miniState 1 (by norm_num) le_rfl) miniActEv (procQ 1 (by norm_num) le_rfl)
      () := by
  intro _ a ha
  simp only [procQ, FinDistr.act2] at ha
  cases a
  · rw [mem_argmaxPlus, miniature_aPlus]
    refine ⟨by simp [procQ], fun b hb => ?_⟩
    cases b
    · exact le_rfl
    · simp [procQ] at hb
  · simp at ha

/-- **`δ_b` is approved vacuously** (`q = 0`).
Source: `calibration.md` CA-13′
Kind: N+ -/
theorem miniature_tEdt_pure_b :
    TEdtAt (fun _ => miniState 0 le_rfl (by norm_num)) miniActEv (procQ 0 le_rfl (by norm_num))
      () := by
  intro _ a ha
  simp only [procQ, FinDistr.act2] at ha
  cases a
  · simp at ha
  · rw [mem_argmaxPlus, miniature_aPlus]
    refine ⟨by simp [procQ], fun b hb => ?_⟩
    cases b
    · simp [procQ] at hb
    · exact le_rfl

/-- **An interior `q` is calibrated-and-approved iff `q = 2/3`** (the tie): with both acts
subjectively possible, `a ∈ argmax ↔ q ≤ 2(1−q)` and `b ∈ argmax ↔ 2(1−q) ≤ q`.
Source: [[decision-problems-v2]] Remark 4.3 ("at `q = 2/3` the values tie"); `calibration.md`
CA-13′
Kind: P
Fidelity: exact
Hyps: (a) `0 < q < 1` -/
theorem miniature_tEdt_interior_iff (q : ℚ) (h0 : 0 < q) (h1 : q < 1) :
    TEdtAt (fun _ => miniState q h0.le h1.le) miniActEv (procQ q h0.le h1.le) () ↔ q = 2 / 3 := by
  have hA : APlus (fun _ => miniState q h0.le h1.le) miniActEv () = Finset.univ := by
    rw [miniature_aPlus]
    ext a; cases a <;> simp [procQ] <;> linarith
  have hVa := miniState_V_a q h0 h1.le
  have hVb := miniState_V_b q h0.le h1
  constructor
  · intro h
    have ha := h ⟨.a, by rw [hA]; simp⟩ .a (by simp [procQ, h0])
    have hb := h ⟨.a, by rw [hA]; simp⟩ .b (by simp [procQ]; linarith)
    rw [mem_argmaxPlus, hA] at ha hb
    have h1' := ha.2 .b (Finset.mem_univ _)
    have h2' := hb.2 .a (Finset.mem_univ _)
    rw [hVa, hVb] at h1' h2'
    linarith
  · rintro rfl
    intro _ a _
    rw [mem_argmaxPlus, hA]
    refine ⟨Finset.mem_univ _, fun b _ => ?_⟩
    cases a <;> cases b <;> simp only [hVa, hVb] <;> norm_num

/-- **Remark 4.3's tie (N+)**: at `q = 2/3` the state `(2/3, 1/3)` is strictly calibrated and
`T_EDT`-approved for `procQ (2/3)` — tie-freedom does existence work.
Source: [[decision-problems-v2]] §4 Remark 4.3
Kind: N+ -/
theorem miniature_tie_approved :
    StrictOC (fun _ => miniState (2/3) (by norm_num) (by norm_num)) miniObs
      (procQ (2/3) (by norm_num) (by norm_num)) miniature ∧
    TEdtAt (fun _ => miniState (2/3) (by norm_num) (by norm_num)) miniActEv
      (procQ (2/3) (by norm_num) (by norm_num)) () :=
  ⟨miniature_strictOC _ _ _,
    (miniature_tEdt_interior_iff (2/3) (by norm_num) (by norm_num)).mpr rfl⟩

/-- `argmaxPlus` on the miniature for interior `q < 2/3` is `{a}`.
Source: `dynamic.md` DY-1(i). Kind: L -/
theorem miniature_argmax_lt (q : ℚ) (h0 : 0 < q) (h1 : q < 2 / 3) (hle : q ≤ 1) :
    argmaxPlus (fun _ => miniState q h0.le hle) miniActEv () = {.a} := by
  have hA : APlus (fun _ => miniState q h0.le hle) miniActEv () = Finset.univ := by
    rw [miniature_aPlus]
    ext a; cases a <;> simp [procQ] <;> linarith
  have hVa := miniState_V_a q h0 hle
  have hVb := miniState_V_b q h0.le (by linarith)
  ext a
  rw [mem_argmaxPlus, hA, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩
    cases a
    · rfl
    · have := h .a (Finset.mem_univ _)
      rw [hVa, hVb] at this
      linarith
  · rintro rfl
    refine ⟨Finset.mem_univ _, fun b _ => ?_⟩
    cases b
    · exact le_rfl
    · rw [hVa, hVb]; linarith

/-- `argmaxPlus` on the miniature for interior `q > 2/3` is `{b}`.
Source: `dynamic.md` DY-1(i). Kind: L -/
theorem miniature_argmax_gt (q : ℚ) (h0 : 2 / 3 < q) (h1 : q < 1) (hge : 0 ≤ q) :
    argmaxPlus (fun _ => miniState q hge h1.le) miniActEv () = {.b} := by
  have hA : APlus (fun _ => miniState q hge h1.le) miniActEv () = Finset.univ := by
    rw [miniature_aPlus]
    ext a; cases a <;> simp [procQ] <;> linarith
  have hVa := miniState_V_a q (by linarith) h1.le
  have hVb := miniState_V_b q hge h1
  ext a
  rw [mem_argmaxPlus, hA, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩
    cases a
    · have := h .b (Finset.mem_univ _)
      rw [hVa, hVb] at this
      linarith
    · rfl
  · rintro rfl
    refine ⟨Finset.mem_univ _, fun b _ => ?_⟩
    cases b
    · rw [hVa, hVb]; linarith
    · exact le_rfl

/-- `argmaxPlus` on the miniature at the tie is everything.
Source: `dynamic.md` DY-1(i). Kind: L -/
theorem miniature_argmax_tie (h0 : (0 : ℚ) ≤ 2 / 3) (h1 : (2 : ℚ) / 3 ≤ 1) :
    argmaxPlus (fun _ => miniState (2/3) h0 h1) miniActEv () = Finset.univ := by
  have hA : APlus (fun _ => miniState (2/3) h0 h1) miniActEv () = Finset.univ := by
    rw [miniature_aPlus]
    ext a; cases a <;> simp [procQ] <;> norm_num
  have hVa := miniState_V_a (2/3) (by norm_num : (0 : ℚ) < 2 / 3) h1
  have hVb := miniState_V_b (2/3) h0 (by norm_num : (2 : ℚ) / 3 < 1)
  ext a
  rw [mem_argmaxPlus, hA]
  simp only [Finset.mem_univ, true_and, iff_true]
  intro b _
  cases a <;> cases b <;> simp only [hVa, hVb] <;> norm_num

/-- **Remark 5.2(i) / DY-1(i) — the fixed-point set of `q ↦ EDT(strictState q)(a)` on the
miniature is exactly `{0, 1}`**: at the tie `2/3` the uniform break returns `½`; at any other
interior `q` the argmax is a singleton and `EDT` returns a pure action; the pure points are fixed
only by self-certainty (`A_d^+` a singleton).
Source: [[decision-problems-v2]] Remark 5.2(i); `dynamic.md` DY-1(i)
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ q ≤ 1` -/
theorem miniature_edt_fixed_iff (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    edtProc (fun _ => miniState q h0 h1) miniActEv () = procQ q h0 h1 () ↔ q = 0 ∨ q = 1 := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have h0' : 0 < q := lt_of_le_of_ne h0 (Ne.symm hc.1)
    have h1' : q < 1 := lt_of_le_of_ne h1 hc.2
    have hw := congrArg (fun p => p.w Act2.a) h
    simp only [procQ, FinDistr.act2_a] at hw
    rcases lt_trichotomy q (2/3) with hlt | heq | hgt
    · rw [edtProc, dif_pos ⟨.a, by rw [miniature_argmax_lt q h0' hlt h1]; simp⟩] at hw
      simp [uniformOn_w, miniature_argmax_lt q h0' hlt h1] at hw
      linarith
    · subst heq
      rw [edtProc, dif_pos ⟨.a, by rw [miniature_argmax_tie h0 h1]; simp⟩] at hw
      simp [uniformOn_w, miniature_argmax_tie h0 h1, Act2.univ_eq] at hw
      norm_num at hw
    · rw [edtProc, dif_pos ⟨.b, by rw [miniature_argmax_gt q hgt h1' h0]; simp⟩] at hw
      simp [uniformOn_w, miniature_argmax_gt q hgt h1' h0] at hw
      linarith
  · rintro (rfl | rfl)
    · apply FinDistr.ext'
      intro a
      have hA : argmaxPlus (fun _ => miniState 0 h0 h1) miniActEv () = {.b} := by
        ext b
        rw [mem_argmaxPlus, miniature_aPlus]
        cases b <;> simp [procQ]
        intro c hc; cases c <;> simp at hc ⊢
      rw [edtProc, dif_pos ⟨.b, by rw [hA]; simp⟩]
      cases a <;> simp [uniformOn_w, hA, procQ]
    · apply FinDistr.ext'
      intro a
      have hA : argmaxPlus (fun _ => miniState 1 h0 h1) miniActEv () = {.a} := by
        ext b
        rw [mem_argmaxPlus, miniature_aPlus]
        cases b <;> simp [procQ]
        intro c hc; cases c <;> simp at hc ⊢
      rw [edtProc, dif_pos ⟨.a, by rw [hA]; simp⟩]
      cases a <;> simp [uniformOn_w, hA, procQ]

/-! ### The miniature is recorded by no procedure (audit round 2, B1) -/

/-- Every leaf of the miniature meets the point `()` exactly twice: the predictor's sample node
and the live node both carry it.
Source: `dynamic.md` DY-1 (the nested reading); audit round 2 B1
Kind: L -/
theorem miniature_count (ℓ : miniature.Leaves) : count () miniature ℓ = 2 := by
  unfold miniature at ℓ ⊢
  rcases ℓ with ⟨s, l, _⟩
  rfl

/-- **No procedure records the miniature at `d`**: some leaf `(a, a)` is positive under `C`
(`C(d)(a) > 0` for some `a`), its world lies in `O = ⊤`, and `dp-core-tree`'s Definition 7
clause (1) would force `count = 1` there, but `count = 2`. Hence CA-12′ and its consequences
(`tie_of_mixed_approved`, `tEdtAt_of_support_subset_of_recordsForAll`) do not apply to the
miniature: self-succession is exactly the case CA-12′ excludes, which is why the miniature's
interior tie at `2/3` (`miniature_tEdt_interior_iff`) is pinned rather than free.
Source: `calibration.md` CA-12′ (self-succession breaks recording); audit round 2 B1 (the
auditors' probes `MiniatureNotRecorded`, adopted)
Kind: N+
Fidelity: exact -/
theorem miniature_not_recordsFor (C : Proc Unit (fun _ => Act2) ℚ) :
    ¬ RecordsFor miniObs miniActEv C miniature () := by
  intro h
  obtain ⟨a, ha⟩ := FinDistr.exists_pos_w' (C ())
  have hpos : 0 < leafLaw C miniature ⟨a, a, ()⟩ := by
    unfold miniature
    simp only [leafLaw_decision, leafLaw_leaf, mul_one]
    exact mul_pos ha ha
  have hcount := (h ⟨a, a, ()⟩ hpos (by simp [miniObs])).1
  rw [miniature_count] at hcount
  exact absurd hcount (by norm_num)

/-- Hence `RecordsForAll` fails on the miniature: the hypothesis of
`V_actEv_eq_of_recordsForAll` and `tEdtAt_of_support_subset_of_recordsForAll` is uninhabited
there.
Source: audit round 2 B1
Kind: L -/
theorem miniature_not_recordsForAll : ¬ RecordsForAll miniObs miniActEv miniature () :=
  fun h => miniature_not_recordsFor (procQ (1/2) (by norm_num) (by norm_num))
    (h (procQ (1/2) (by norm_num) (by norm_num)))

end miniature

end Cleanroom.Decision.DpCalibration
