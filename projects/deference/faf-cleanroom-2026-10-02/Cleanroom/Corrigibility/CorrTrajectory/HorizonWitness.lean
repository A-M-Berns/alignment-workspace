import Cleanroom.Corrigibility.CorrTrajectory.Horizon
import Cleanroom.Corrigibility.CorrTrajectory.Margin

/-!
# `corr-trajectory` — `HorizonWitness`: A6 (the identity refuted) and C7 (three rounds under (MI))

* **A6**: one round, `ε = 1/10`, magnitudes `H ∈ {1, 9}` equiprobable given `W = 1`, `β(1) = 1/2`,
  `β(9) = 1`: the true compliance harm is `1/40`; the identity `E*[harm_t ∣ 𝓕_t^-] =
  ε_t (1 − β_t) h_t` with `β̄ = 3/4`, `h̄ = 5` gives `1/8`; the `β^min = 1/2` bound `1/40 ≤ 1/4`
  survives (`(βmin)` discharged on the process). **Scope** (audit r1, adversarial B2(c)): the process
  is the *final's* S2, where the press may depend on the magnitude. In the develop's own S2 step 3
  (`Pr_t ∼ Bern(β_t)` if `W_t = 1`, `β_t` a function of `W_t` alone) the identity holds, because
  (MI) is built in; what A6 refutes is the identity for a magnitude-dependent press, and the develop's
  Summary compression "exactly `∑ ε_t(1 − β_t) h_t`" stated without that assumption (adversary item 67).
* **C7**: three independent rounds with `(ε, β, α, h, c) = (1/10, 9/10, 1/20, 20, 1)`,
  `(1/50, 4/5, 1/20, 30, 2)`, `(1/200, 1/2, 1/100, 50, 3)`: compliance harm `89/200`, defiance harm
  `57/20`, omission `3457/20000`, computed on the process through `harm_eq_detection` (with `(MI)`
  discharged on every pre-press atom, `detectionEq`), `defiance`, and `omit_eq_detection` (with `(MI)`
  for the false press discharged on every pre-press atom, `detectionEqUB`; repair round 2).
* **A6 through the theorem** (`a6_surviving`, repair round 2): `expect_harm_le 0` applied to the A6
  process at `β^min = 1/2`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrJointProcess
open Finset hiding expect

/-! ### A6 -/

namespace A6

/-- A6's law on `(W, big, Pr)`: `1/40` at `(W, small, Pr)`, `1/40` at `(W, small, ¬Pr)`, `1/20` at
`(W, big, Pr)`, `9/10` at `(¬W, small, ¬Pr)`.
Source: [[corr-wf14-inventory]] 2-020 / invariant-adversary.md item 13; counterexamples.py A6
Kind: D
Fidelity: exact -/
noncomputable def massA6 : Bool × Bool × Bool → ℝ
  | (true, false, true) => 1 / 40
  | (true, false, false) => 1 / 40
  | (true, true, true) => 1 / 20
  | (true, true, false) => 0
  | (false, false, false) => 9 / 10
  | (false, _, _) => 0

/-- `law` (supporting def). Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def law : Distr (Bool × Bool × Bool) where
  mass := massA6
  nonneg ω := by
    rcases ω with ⟨w, b, p⟩
    cases w <;> cases b <;> cases p <;> simp [massA6] <;> norm_num
  sum_eq_one := by simp [Fintype.sum_prod_type, massA6]; norm_num

/-- `expect_law` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_law (f : Bool × Bool × Bool → ℝ) :
    expect law f = 1 / 40 * f (true, false, true) + 1 / 40 * f (true, false, false) +
      1 / 20 * f (true, true, true) + 9 / 10 * f (false, false, false) := by
  simp [expect, Fintype.sum_prod_type, law, massA6]; ring

/-- The pre-press filtration: trivial at `0`, everything after. Source: A6. Kind: D. Fidelity: exact -/
def pre : Atoms (Bool × Bool × Bool) where
  fib t ω := if t = 0 then univ else {ω}
  mem_fib t ω := by rcases t with _ | t <;> simp
  fib_eq_of_mem t ω ω' h := by
    rcases t with _ | t
    · rfl
    · simp at h; rw [h]
  fib_succ_subset t ω := by rcases t with _ | t <;> simp

/-- **The A6 process**: magnitude `big ∈ Bool` with `hOf big = 9`, `hOf small = 1`; compliance always.
Source: [[corr-wf14-inventory]] 2-020 / counterexamples.py A6
Kind: D
Fidelity: exact -/
noncomputable def proc : ShutdownProc (Bool × Bool × Bool) Bool where
  μ := law
  F := Atoms.discrete
  Fpre := pre
  post_subset_pre t ω := by
    rcases t with _ | t <;> simp [Atoms.discrete, pre]
  pre_succ_subset_post t ω := by
    rcases t with _ | t <;> simp [Atoms.discrete, pre]
  wrong _ ω := ω.1
  mag _ ω := ω.2.1
  hOf b := if b then 9 else 1
  cOf _ := 0
  hOf_nonneg b := by cases b <;> norm_num
  cOf_nonneg _ := le_rfl
  pressed _ ω := ω.2.2
  pressed_meas _ := Atoms.meas_discrete _ _
  kappa _ _ := true
  kappa_meas _ _ _ _ := rfl
  irr _ _ := false
  cat _ _ := false
  cat_absorbing _ _ _ h := h

/-- `harm_fun` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma harm_fun : proc.harm 0 = fun ω => if ω.1 then (if ω.2.2 then 0 else (if ω.2.1 then 9 else 1)) else 0 := by
  funext ω
  rw [proc.harm_of_kappa 0 ω rfl]
  rcases ω with ⟨w, b, p⟩
  cases w <;> cases b <;> cases p <;> simp [proc, indB, ShutdownProc.H]

/-- **A6 — refutes the Statement 4 identity** `E*[harm_t ∣ 𝓕_t^-] = ε_t (1 − β_t) h_t` **in the final's
S2** (magnitude-dependent press, no `(MI)`): the true compliance harm is `1/40`, the identity's value
with `ε = 1/10`, `β̄ = 3/4`, `h̄ = 5` (all three the process's own product-form conditionals) is `1/8`.
In the develop's own S2 step 3 the press depends on `W_t` alone, so there the identity holds — (MI) is
built in, unflagged; the develop's Summary states "exactly" without it (adversary item 67). Surviving
neighbour: the `β^min` bound `expect_harm_le` at `β^min = 1/2`: `1/40 ≤ 1/4`; equality under `(MI)`.
Source: [[corr-wf14-inventory]] 2-020 / invariant.md Statement 4 and Summary ("expected harm through any horizon is *exactly* `∑_t ε_t(1 − β_t) h_t`"), S2 step 3 l. 28; invariant-final.md S2 step 3 ((MI)); counterexamples.py A6
Kind: N+ (refutation, scoped: the identity fails once the press may depend on the magnitude)
Fidelity: exact (the final's S2; the develop's S2 has (MI) built in)
Hyps: (a) only -/
theorem a6 :
    expect proc.μ (proc.harm 0) = 1 / 40 ∧
      expect proc.μ (indB (proc.wrong 0)) = 1 / 10 ∧
      expect proc.μ (fun ω => indB (proc.wrong 0) ω * indB (proc.pressed 0) ω) / expect proc.μ (indB (proc.wrong 0)) = 3 / 4 ∧
      expect proc.μ (fun ω => indB (proc.wrong 0) ω * proc.H 0 ω) / expect proc.μ (indB (proc.wrong 0)) = 5 ∧
      (1 / 10 : ℝ) * (1 - 3 / 4) * 5 = 1 / 8 ∧ (1 / 40 : ℝ) ≠ 1 / 8 ∧
      proc.detectionLB (fun _ _ => 1 / 2) 0 ∧
      expect proc.μ (fun ω => (1 - (1 / 2 : ℝ)) * (indB (proc.wrong 0) ω * proc.H 0 ω)) = 1 / 4 := by
  have hμ : proc.μ = law := rfl
  have hW : expect proc.μ (indB (proc.wrong 0)) = 1 / 10 := by
    rw [hμ, expect_law]; simp [proc, indB]; norm_num
  refine ⟨?_, hW, ?_, ?_, by norm_num, by norm_num, ?_, ?_⟩
  · rw [harm_fun, hμ, expect_law]; norm_num
  · rw [hW, hμ, expect_law]; simp [proc, indB]; norm_num
  · rw [hW, hμ, expect_law]; simp [proc, indB, ShutdownProc.H]; norm_num
  · intro ω m
    have hfib : proc.Fpre.fib 0 ω = univ := rfl
    unfold condSum
    rw [hfib]
    show (1 / 2 : ℝ) * expect law _ ≤ expect law _
    rw [expect_law, expect_law]
    cases m <;> simp [proc, indB, ShutdownProc.magInd] <;> norm_num
  · rw [hμ, expect_law]; simp [proc, indB, ShutdownProc.H]; norm_num

/-- **A6's surviving neighbour obtained through the theorem** (audit r2, fidelity N5 / adversarial
N6): `expect_harm_le 0` at `β^min = 1/2`, with `(βmin)` discharged on the A6 process (`a6`), gives
`E*[harm₀] ≤ E*[(1 − 1/2) W₀ H₀]`, and the right-hand side is `1/4` (the left is `1/40`, `a6`).
Source: [[corr-wf14-inventory]] 2-020 / invariant-final.md Statement 4 (the `β^min` bound on A6); counterexamples.py A6
Kind: N+ (`expect_harm_le` applied; `1/40 ≤ 1/4` strict)
Fidelity: exact
Hyps: (a) only -/
theorem a6_surviving :
    expect proc.μ (proc.harm 0) ≤
        expect proc.μ (fun ω => (1 - (1 / 2 : ℝ)) * (indB (proc.wrong 0) ω * proc.H 0 ω)) ∧
      expect proc.μ (fun ω => (1 - (1 / 2 : ℝ)) * (indB (proc.wrong 0) ω * proc.H 0 ω)) = 1 / 4 :=
  ⟨proc.expect_harm_le 0 (fun _ _ => 1 / 2) (fun _ => rfl) a6.2.2.2.2.2.2.1 (proc.Fpre.meas_const 0 _),
    a6.2.2.2.2.2.2.2⟩

end A6

/-! ### C7 -/

namespace C7

open Margin (cell expect_cell)

/-- The three rounds' parameters `(ε, β, α, h, c)` by round index.
Source: checks.py C7. Kind: D. Fidelity: exact -/
noncomputable def epsN (t : ℕ) : ℝ := if t = 0 then 1 / 10 else if t = 1 then 1 / 50 else 1 / 200
/-- `betaN` (supporting def). Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def betaN (t : ℕ) : ℝ := if t = 0 then 9 / 10 else if t = 1 then 4 / 5 else 1 / 2
/-- `alphaN` (supporting def). Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def alphaN (t : ℕ) : ℝ := if t = 0 then 1 / 20 else if t = 1 then 1 / 20 else 1 / 100
/-- `hh` (supporting def). Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def hh : Fin 3 → ℝ := ![20, 30, 50]
/-- `cc` (supporting def). Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def cc : Fin 3 → ℝ := ![1, 2, 3]

/-- `eps_mem` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma eps_mem (t : ℕ) : epsN t ∈ Set.Icc (0 : ℝ) 1 := by unfold epsN; split_ifs <;> norm_num
/-- `beta_mem` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma beta_mem (t : ℕ) : betaN t ∈ Set.Icc (0 : ℝ) 1 := by unfold betaN; split_ifs <;> norm_num
/-- `alpha_mem` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma alpha_mem (t : ℕ) : alphaN t ∈ Set.Icc (0 : ℝ) 1 := by unfold alphaN; split_ifs <;> norm_num

/-- The round-`t` cell. Source: checks.py C7. Kind: D. Fidelity: exact -/
noncomputable def cellI (t : ℕ) : Distr (World × Bool) :=
  cell (epsN t) (alphaN t) (betaN t) (eps_mem t) (alpha_mem t) (beta_mem t)

/-- `Ω3` (supporting abbrev). Source: none: infrastructure. Kind: D. Fidelity: n/a -/
abbrev Ω3 := (World × Bool) × ((World × Bool) × (World × Bool))

/-- The three-round law. Source: checks.py C7. Kind: D. Fidelity: exact -/
noncomputable def law : Distr Ω3 := prod2 (cellI 0) (prod2 (cellI 1) (cellI 2))

/-- `𝓕_t`: rounds `≤ t`. Source: invariant-final.md S1. Kind: D. Fidelity: exact -/
def post : Atoms Ω3 where
  fib t ω := if t = 0 then univ.filter (fun ω' => ω'.1 = ω.1)
    else if t = 1 then univ.filter (fun ω' => ω'.1 = ω.1 ∧ ω'.2.1 = ω.2.1) else {ω}
  mem_fib t ω := by rcases t with _ | _ | t <;> simp
  fib_eq_of_mem t ω ω' h := by
    rcases t with _ | _ | t
    · simp at h; simp [h]
    · simp at h; simp [h]
    · simp at h; rw [h]
  fib_succ_subset t ω := by
    rcases t with _ | _ | t
    · intro ω' h; simp at h; simp [h]
    · intro ω' h; simp at h; simp [h]
    · simp

/-- `𝓕_t^-`: rounds `< t`. Source: invariant-final.md S1. Kind: D. Fidelity: exact -/
def pre : Atoms Ω3 where
  fib t ω := if t = 0 then univ else if t = 1 then univ.filter (fun ω' => ω'.1 = ω.1)
    else if t = 2 then univ.filter (fun ω' => ω'.1 = ω.1 ∧ ω'.2.1 = ω.2.1) else {ω}
  mem_fib t ω := by rcases t with _ | _ | _ | t <;> simp
  fib_eq_of_mem t ω ω' h := by
    rcases t with _ | _ | _ | t
    · rfl
    · simp at h; simp [h]
    · simp at h; simp [h]
    · simp at h; rw [h]
  fib_succ_subset t ω := by
    rcases t with _ | _ | _ | t
    · simp
    · intro ω' h; simp at h; simp [h]
    · intro ω' h; simp at h; simp [h]
    · simp

/-- The coordinate of round `t` (`t ≥ 3` reads round `2`). Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def coord (t : ℕ) (ω : Ω3) : World × Bool := if t = 0 then ω.1 else if t = 1 then ω.2.1 else ω.2.2

/-- **The C7 process** with compliance flag `κ` (constant): `κ = true` complies, `false` defies.
Source: [[corr-wf14-inventory]] 2-080 (C7) / checks.py C7
Kind: D
Fidelity: exact -/
noncomputable def proc (κ : Bool) : ShutdownProc Ω3 (Fin 3) where
  μ := law
  F := post
  Fpre := pre
  post_subset_pre t ω := by
    rcases t with _ | _ | _ | t
    · simp [post, pre]
    · intro ω' h; simp [post] at h; simp [pre, h]
    · intro ω' h; simp [post] at h; simp [pre, h]
    · simp [post, pre]
  pre_succ_subset_post t ω := by
    rcases t with _ | _ | _ | t
    · simp [post, pre]
    · intro ω' h; simp [pre] at h; simp [post, h]
    · simp [post, pre]
    · simp [post, pre]
  wrong t ω := decide ((coord t ω).1 = .wrong)
  mag t _ := if t = 0 then 0 else if t = 1 then 1 else 2
  hOf i := hh i
  cOf i := cc i
  hOf_nonneg i := by fin_cases i <;> simp [hh] <;> norm_num
  cOf_nonneg i := by fin_cases i <;> simp [cc] <;> norm_num
  pressed t ω := (coord t ω).2
  pressed_meas t ω ω' hω' := by
    rcases t with _ | _ | _ | t
    · simp [post] at hω'; simp [indB, coord, hω']
    · simp [post] at hω'; simp [indB, coord, hω']
    · simp [post] at hω'; simp [indB, coord, hω']
    · simp [post] at hω'; simp [hω']
  kappa _ _ := κ
  kappa_meas _ _ _ _ := rfl
  irr _ _ := false
  cat _ _ := false
  cat_absorbing _ _ _ h := h

/-- `proc_μ` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma proc_μ (κ : Bool) : (proc κ).μ = law := rfl

/-- Expectations of per-round functions under the three-round law.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_coord0 (g : World × Bool → ℝ) : expect law (fun ω => g (coord 0 ω)) = expect (cellI 0) g :=
  expect_prod2_fst _ _ g

/-- `expect_coord1` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_coord1 (g : World × Bool → ℝ) : expect law (fun ω => g (coord 1 ω)) = expect (cellI 1) g :=
  (expect_prod2_snd (cellI 0) (prod2 (cellI 1) (cellI 2)) (fun p => g p.1)).trans (expect_prod2_fst _ _ g)

/-- `expect_coord2` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_coord2 (g : World × Bool → ℝ) : expect law (fun ω => g (coord 2 ω)) = expect (cellI 2) g :=
  (expect_prod2_snd (cellI 0) (prod2 (cellI 1) (cellI 2)) (fun p => g p.2)).trans (expect_prod2_snd _ _ g)

/-- The sum over the round-`0` atom of a function of round `1`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_atom1 (g : World × Bool → ℝ) (a : World × Bool) :
    ∑ ω ∈ univ.filter (fun ω : Ω3 => ω.1 = a), law.mass ω * g ω.2.1 = (cellI 0).mass a * expect (cellI 1) g := by
  have h := sum_filter_fst (cellI 0) (prod2 (cellI 1) (cellI 2)) a (fun p => g p.1)
  refine h.trans ?_
  congr 1
  exact expect_prod2_fst (cellI 1) (cellI 2) g

/-- The sum over the rounds-`0,1` atom of a function of round `2`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_atom2 (g : World × Bool → ℝ) (a b : World × Bool) :
    ∑ ω ∈ univ.filter (fun ω : Ω3 => ω.1 = a ∧ ω.2.1 = b), law.mass ω * g ω.2.2 =
      (cellI 0).mass a * ((cellI 1).mass b * expect (cellI 2) g) := by
  rw [show law.mass = (prod2 (cellI 0) (prod2 (cellI 1) (cellI 2))).mass from rfl]
  rw [sum_filter, Fintype.sum_prod_type]
  simp only [prod2_mass]
  rw [Finset.sum_eq_single a]
  · simp only [true_and]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
    · simp only [if_true]
      unfold expect
      rw [Finset.mul_sum, Finset.mul_sum]
      refine sum_congr rfl fun c _ => by ring
    · intro b' _ hb'; simp [hb']
    · intro h; exact absurd (mem_univ b) h
  · intro a' _ ha'; simp [ha']
  · intro h; exact absurd (mem_univ a) h

/-- The integrands of `(MI)`: `W · 𝟙[mag = m] · Pr` and `W · 𝟙[mag = m]` on a cell point, round `t`.
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def gW (m : Fin 3) (t : ℕ) (p : World × Bool) : ℝ :=
  (if p.1 = .wrong then (1 : ℝ) else 0) * (if (if t = 0 then (0 : Fin 3) else if t = 1 then 1 else 2) = m then 1 else 0)

/-- `gWP` (supporting def). Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def gWP (m : Fin 3) (t : ℕ) (p : World × Bool) : ℝ := gW m t p * (if p.2 then 1 else 0)

/-- `expect_cell_gWP` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_cell_gWP (m : Fin 3) (t : ℕ) :
    expect (cellI t) (gWP m t) = betaN t * expect (cellI t) (gW m t) := by
  unfold cellI; rw [expect_cell, expect_cell]; simp [gWP, gW]; split_ifs <;> ring

/-- **`(MI)` holds on every pre-press atom** of the C7 process with `β_t = betaN t`.
Source: checks.py C7 (the rows' `β`). Kind: L. Fidelity: exact -/
theorem detectionEq (κ : Bool) (t : ℕ) (ht : t ≤ 2) : (proc κ).detectionEq (fun t _ => betaN t) t := by
  intro ω m
  have e1 : ∀ ω' : Ω3, indB ((proc κ).wrong t) ω' * (proc κ).magInd t m ω' * indB ((proc κ).pressed t) ω' =
      gWP m t (coord t ω') := by
    intro ω'; simp [proc, indB, ShutdownProc.magInd, gWP, gW]
  have e2 : ∀ ω' : Ω3, indB ((proc κ).wrong t) ω' * (proc κ).magInd t m ω' = gW m t (coord t ω') := by
    intro ω'; simp [proc, indB, ShutdownProc.magInd, gW]
  unfold condSum
  simp only [e1]
  simp only [e2, proc_μ]
  interval_cases t
  · have hfib : (proc κ).Fpre.fib 0 ω = univ := rfl
    rw [hfib]
    show expect law _ = _ * expect law _
    rw [expect_coord0 (gWP m 0), expect_coord0 (gW m 0), expect_cell_gWP]
  · have hfib : (proc κ).Fpre.fib 1 ω = univ.filter (fun ω' : Ω3 => ω'.1 = ω.1) := by simp [proc, pre]
    rw [hfib]
    have c1 : ∀ ω' : Ω3, coord 1 ω' = ω'.2.1 := fun _ => rfl
    simp only [c1]
    rw [sum_atom1 (gWP m 1), sum_atom1 (gW m 1), expect_cell_gWP]; ring
  · have hfib : (proc κ).Fpre.fib 2 ω = univ.filter (fun ω' : Ω3 => ω'.1 = ω.1 ∧ ω'.2.1 = ω.2.1) := by
      simp [proc, pre]
    rw [hfib]
    have c2 : ∀ ω' : Ω3, coord 2 ω' = ω'.2.2 := fun _ => rfl
    simp only [c2]
    rw [sum_atom2 (gWP m 2), sum_atom2 (gW m 2), expect_cell_gWP]; ring

/-- The integrands of `(MI)` for the false press: `¬W · 𝟙[mag = m] · Pr` and `¬W · 𝟙[mag = m]` on a
cell point, round `t` (the duals of `gWP`, `gW`; repair round 2).
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def gNW (m : Fin 3) (t : ℕ) (p : World × Bool) : ℝ :=
  (1 - (if p.1 = .wrong then (1 : ℝ) else 0)) * (if (if t = 0 then (0 : Fin 3) else if t = 1 then 1 else 2) = m then 1 else 0)

/-- `gNWP` (supporting def). Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def gNWP (m : Fin 3) (t : ℕ) (p : World × Bool) : ℝ := gNW m t p * (if p.2 then 1 else 0)

/-- `expect_cell_gNWP` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_cell_gNWP (m : Fin 3) (t : ℕ) :
    expect (cellI t) (gNWP m t) = alphaN t * expect (cellI t) (gNW m t) := by
  unfold cellI; rw [expect_cell, expect_cell]; simp [gNWP, gNW]; split_ifs <;> ring

/-- **`(MI)` for the false press holds on every pre-press atom** of the C7 process with
`α_t = alphaN t` (repair round 2, audit r2 fidelity B1).
Source: checks.py C7 (the rows' `α`). Kind: L. Fidelity: exact -/
theorem detectionEqUB (κ : Bool) (t : ℕ) (ht : t ≤ 2) : (proc κ).detectionEqUB (fun t _ => alphaN t) t := by
  intro ω m
  have e1 : ∀ ω' : Ω3, (1 - indB ((proc κ).wrong t) ω') * (proc κ).magInd t m ω' * indB ((proc κ).pressed t) ω' =
      gNWP m t (coord t ω') := by
    intro ω'; simp [proc, indB, ShutdownProc.magInd, gNWP, gNW]
  have e2 : ∀ ω' : Ω3, (1 - indB ((proc κ).wrong t) ω') * (proc κ).magInd t m ω' = gNW m t (coord t ω') := by
    intro ω'; simp [proc, indB, ShutdownProc.magInd, gNW]
  unfold condSum
  simp only [e1]
  simp only [e2, proc_μ]
  interval_cases t
  · have hfib : (proc κ).Fpre.fib 0 ω = univ := rfl
    rw [hfib]
    show expect law _ = _ * expect law _
    rw [expect_coord0 (gNWP m 0), expect_coord0 (gNW m 0), expect_cell_gNWP]
  · have hfib : (proc κ).Fpre.fib 1 ω = univ.filter (fun ω' : Ω3 => ω'.1 = ω.1) := by simp [proc, pre]
    rw [hfib]
    have c1 : ∀ ω' : Ω3, coord 1 ω' = ω'.2.1 := fun _ => rfl
    simp only [c1]
    rw [sum_atom1 (gNWP m 1), sum_atom1 (gNW m 1), expect_cell_gNWP]; ring
  · have hfib : (proc κ).Fpre.fib 2 ω = univ.filter (fun ω' : Ω3 => ω'.1 = ω.1 ∧ ω'.2.1 = ω.2.1) := by
      simp [proc, pre]
    rw [hfib]
    have c2 : ∀ ω' : Ω3, coord 2 ω' = ω'.2.2 := fun _ => rfl
    simp only [c2]
    rw [sum_atom2 (gNWP m 2), sum_atom2 (gNW m 2), expect_cell_gNWP]; ring

/-- The harm integrand `a · W · b` and the omission-bound integrand `a · (1 − W) · c` on a cell point.
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def gH (a b : ℝ) (p : World × Bool) : ℝ := a * ((if p.1 = .wrong then (1 : ℝ) else 0) * b)
/-- `gC` (supporting def). Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def gC (a c : ℝ) (p : World × Bool) : ℝ := a * ((1 - (if p.1 = .wrong then (1 : ℝ) else 0)) * c)

/-- `expect_cell_gH` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_cell_gH (t : ℕ) (a b : ℝ) : expect (cellI t) (gH a b) = a * (epsN t * b) := by
  unfold cellI; rw [expect_cell]; simp [gH] <;> ring

/-- `expect_cell_gC` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_cell_gC (t : ℕ) (a c : ℝ) : expect (cellI t) (gC a c) = a * ((1 - epsN t) * c) := by
  unfold cellI; rw [expect_cell]; simp [gC] <;> ring

/-- `harmW` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma harmW (κ : Bool) (t : ℕ) (ht : t ≤ 2) (a : ℝ) :
    (fun ω : Ω3 => a * (indB ((proc κ).wrong t) ω * (proc κ).H t ω)) =
      fun ω => gH a (hh ⟨t, by omega⟩) (coord t ω) := by
  funext ω
  interval_cases t <;> simp [proc, indB, ShutdownProc.H, gH]

/-- `omitC` (supporting lemma): the omission-bound integrand of `omit_eq_detection` on a cell point.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma omitC (t : ℕ) (ht : t ≤ 2) (a : ℝ) :
    (fun ω : Ω3 => a * ((1 - indB ((proc true).wrong t) ω) * (proc true).C t ω)) =
      fun ω => gC a (cc ⟨t, by omega⟩) (coord t ω) := by
  funext ω
  interval_cases t <;> simp [proc, indB, ShutdownProc.C, gC]

/-- **C7 (N+): three rounds under `(MI)`** — compliance harm `89/200` (through `harm_eq_detection`
with `(MI)` discharged on every atom), defiance harm `57/20` (through `defiance`), omission under
compliance `3457/20000` (through `omit_eq_detection` with `(MI)` for the false press discharged on
every atom, `detectionEqUB`; repair round 2 — before it the omission was computed pointwise).
Source: [[corr-wf14-inventory]] 2-080 (C7) / invariant-final.md Statement 4 ("C7 evaluates a three-round (MI) instance"); checks.py C7
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem c7 :
    expect (proc true).μ ((proc true).Harm 2) = 89 / 200 ∧
      expect (proc false).μ ((proc false).Harm 2) = 57 / 20 ∧
      expect (proc true).μ ((proc true).Omit 2) = 3457 / 20000 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [(proc true).harm_eq_detection 2 (fun t _ => betaN t) (fun _ _ _ => rfl)
      (fun t ht => detectionEq true t ht) (fun t _ => (proc true).Fpre.meas_const t _)]
    simp only [sum_range_succ, sum_range_zero, zero_add]
    rw [harmW true 0 (by norm_num), harmW true 1 (by norm_num), harmW true 2 (by norm_num), proc_μ,
      expect_coord0 (gH _ _), expect_coord1 (gH _ _), expect_coord2 (gH _ _), expect_cell_gH, expect_cell_gH,
      expect_cell_gH]
    simp [epsN, betaN, hh]; norm_num
  · have hd := (proc false).defiance 2 (fun _ _ _ => rfl)
    have e : (proc false).Harm 2 = fun ω => ∑ t ∈ range 3, 1 * (indB ((proc false).wrong t) ω * (proc false).H t ω) := by
      funext ω; rw [(hd ω).1]; simp
    rw [e, expect_sum_range]
    simp only [sum_range_succ, sum_range_zero, zero_add]
    rw [harmW false 0 (by norm_num), harmW false 1 (by norm_num), harmW false 2 (by norm_num), proc_μ,
      expect_coord0 (gH _ _), expect_coord1 (gH _ _), expect_coord2 (gH _ _), expect_cell_gH, expect_cell_gH,
      expect_cell_gH]
    simp [epsN, hh]; norm_num
  · rw [(proc true).omit_eq_detection 2 (fun t _ => alphaN t) (fun _ _ _ => rfl)
      (fun t ht => detectionEqUB true t ht) (fun t _ => (proc true).Fpre.meas_const t _)]
    simp only [sum_range_succ, sum_range_zero, zero_add]
    rw [omitC 0 (by norm_num), omitC 1 (by norm_num), omitC 2 (by norm_num), proc_μ,
      expect_coord0 (gC _ _), expect_coord1 (gC _ _), expect_coord2 (gC _ _), expect_cell_gC, expect_cell_gC,
      expect_cell_gC]
    simp [epsN, alphaN, cc]; norm_num

end C7

end Cleanroom.Corrigibility.CorrTrajectory
