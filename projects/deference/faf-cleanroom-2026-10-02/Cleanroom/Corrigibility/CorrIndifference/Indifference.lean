import Cleanroom.Corrigibility.CorrIndifference.Soares

/-!
# Utility indifference: the §3 utility and Theorems 3–6 (D-3, T4–T6), Fallenstein's policy lemma (T13)

The indifferent utility `U := U_N` off `Press`, `U_S + f(a₁)` on it, with
`f(a₁) := vN(a₁) − vS(a₁)` (eqs. 11–13; non-circular by eq. 14 = `best_add_const`). The whole
positive content of §3 is **one identity**, `EU_indiffU_eq_vN`: `E[U ; a₁] = vN(a₁)`, proved in
product form and *unconditionally* (both sides are the junk `0` at `p(Press ; a₁) = 1`; at
`p(Press ; a₁) = 0` the `vS` inside `f` is junk but multiplies mass `0`). Theorems 4, 5, 6 and
the `U_S`-invariance are that identity read at one or two actions.

Source: [[corr-refs-inventory]] 005–007 → soares-2015 §3 eqs. (11)–(15), Theorems 3–5
(l. 200–262), §4.1 Theorem 6 (l. 263–290); 011 → fallenstein-2015 (l. 28–58).
-/

namespace Cleanroom.Corrigibility.CorrIndifference

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep

set_option linter.unusedSectionVars false

namespace SoaresModel

variable {O A₁ A₂ : Type*} [Fintype O] [DecidableEq O] [Fintype A₂] [Nonempty A₂]
variable (M : SoaresModel O A₁ A₂)

/-! ## D-3. The correction and the indifferent utility -/

/-- **The correction term** `f(a₁) := E[U_N | O ∉ Press ; a₁] − E[U_S | O ∈ Press ; a₁]`
(eq. 13), as the difference of the two derived quotients (junk values disclosed at `vN`, `vS`).
Source: [[corr-refs-inventory]] 005 / soares-2015 §3 eq. (13)
Kind: D
Fidelity: exact -/
noncomputable def f (UN US : A₁ → O → A₂ → ℝ) (a : A₁) : ℝ := M.vN UN a - M.vS US a

/-- **D-3. The indifferent utility** (eq. 11): `U_N` off `Press`, `U_S + f(a₁)` on it.
Source: [[corr-refs-inventory]] 005 / soares-2015 §3 eq. (11)
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def indiffU (UN US : A₁ → O → A₂ → ℝ) : A₁ → O → A₂ → ℝ :=
  fun a o b => if o ∈ M.Press then US a o b + M.f UN US a else UN a o b

/-- On `Press` the indifferent utility's best value is `U_S`'s plus `f(a₁)` (eq. 14 in value form).
Source: [[corr-refs-inventory]] 006 / soares-2015 eq. (14)
Kind: L
Fidelity: exact -/
lemma best_indiffU_of_mem_press {UN US : A₁ → O → A₂ → ℝ} {a : A₁} {o : O} (ho : o ∈ M.Press) :
    best (M.indiffU UN US) a o = best US a o + M.f UN US a :=
  best_add_const fun b => by simp only [indiffU, if_pos ho]

/-- Off `Press` the indifferent utility's best value is `U_N`'s.
Source: [[corr-refs-inventory]] 005 / soares-2015 eq. (11)
Kind: L
Fidelity: exact -/
lemma best_indiffU_of_not_mem_press {UN US : A₁ → O → A₂ → ℝ} {a : A₁} {o : O}
    (ho : o ∉ M.Press) : best (M.indiffU UN US) a o = best UN a o :=
  best_congr fun b => by simp only [indiffU, if_neg ho]

/-! ## T4. The identity (Theorem 4's core) -/

/-- **The press branch of the indifferent utility, product form:**
`∑_{o ∈ Press} p(o) best_U(o) = p(Press) · vN(a₁)` — the penalty term cancels `U_S`'s
expectation and the bonus term supplies `vN`. Unconditional: at `p(Press) = 0` the `vS`
inside `f` is junk but every summand has mass `0`.
Source: [[corr-refs-inventory]] 005 / soares-2015 Theorem 4 proof, eq. (15)
Kind: L
Fidelity: exact (product form; the conditional form is `condPress_indiffU` under `0 < p(Press)`) -/
theorem branchSum_indiffU_press (UN US : A₁ → O → A₂ → ℝ) (a : A₁) :
    M.branchSum (M.indiffU UN US) a M.Press = M.pressMass a * M.vN UN a := by
  rw [M.branchSum_eq_of_best_add (fun o ho => M.best_indiffU_of_mem_press ho),
    M.branchSum_press_eq_mul_vS, ← M.pressMass_eq_sum]
  unfold f; ring

/-- **The silence branch of the indifferent utility, product form:**
`∑_{o ∉ Press} p(o) best_U(o) = (1 − p(Press)) · vN(a₁)` (eq. 11 off `Press`, then eq. 7).
Source: [[corr-refs-inventory]] 005 / soares-2015 Theorem 4 proof
Kind: L
Fidelity: exact -/
theorem branchSum_indiffU_compl (UN US : A₁ → O → A₂ → ℝ) (a : A₁) :
    M.branchSum (M.indiffU UN US) a M.Pressᶜ = (1 - M.pressMass a) * M.vN UN a := by
  rw [M.branchSum_congr (fun o ho => M.best_indiffU_of_not_mem_press (mem_compl.mp ho)),
    M.branchSum_compl_eq_mul_vN]

/-- **The identity (Theorem 4's core, eq. 15):** `E[U ; a₁] = vN(a₁) = E[U_N | O ∉ Press ; a₁]`
for the indifferent utility, *for every* `U_S` and every `a₁`. Unconditional as an equation of
reals; it is *meaningful* only where `vN` is the conditional value it names, i.e. under
`p(Press ; a₁) < 1` — at `p(Press ; a₁) = 1` both sides are the junk `0` (see `vN`). This is the
paper's entire positive result; Theorems 4–6 read it at one or two actions.
Source: [[corr-refs-inventory]] 005 / soares-2015 Theorem 4 proof (eq. 15); corr-core-020
Kind: L
Fidelity: exact (product form throughout; no `0 < p < 1` needed for the equation) -/
theorem EU_indiffU_eq_vN (UN US : A₁ → O → A₂ → ℝ) (a : A₁) :
    M.EU (M.indiffU UN US) a = M.vN UN a := by
  rw [M.EU_eq_branchSum_add_compl, M.branchSum_indiffU_press, M.branchSum_indiffU_compl]; ring

/-- The conditional form on `Press`: `E[U | O ∈ Press ; a₁] = vN(a₁)` under `0 < p(Press ; a₁)`
(derived from the product form; the source's eq. 15 first display).
Source: [[corr-refs-inventory]] 005 / soares-2015 eq. (15)
Kind: L
Fidelity: exact -/
theorem condPress_indiffU (UN US : A₁ → O → A₂ → ℝ) (a : A₁) (h : 0 < M.pressMass a) :
    M.branchSum (M.indiffU UN US) a M.Press / M.pressMass a = M.vN UN a := by
  rw [M.branchSum_indiffU_press]; field_simp

/-- The conditional form off `Press`: `E[U | O ∉ Press ; a₁] = vN(a₁)` under `p(Press ; a₁) < 1`.
Source: [[corr-refs-inventory]] 005 / soares-2015 eq. (15)
Kind: L
Fidelity: exact -/
theorem condSilent_indiffU (UN US : A₁ → O → A₂ → ℝ) (a : A₁) (h : M.pressMass a < 1) :
    M.branchSum (M.indiffU UN US) a M.Pressᶜ / (1 - M.pressMass a) = M.vN UN a := by
  rw [M.branchSum_indiffU_compl]; have : 1 - M.pressMass a ≠ 0 := by linarith
  field_simp

/-- **Theorem 4 (boundary form).** `vN(a♯) < vN(a⋆) ⟹ E[U ; a♯] < E[U ; a⋆]`, needing only
`p(Press ; ·) < 1` at both actions (so that both `vN` are the conditional values the hypothesis
compares; the identity itself needs nothing). At `p(Press ; a) = 0` the `vS(a)` inside `f(a)` is
the junk `0`, but it multiplies mass `0` — Fallenstein 2014's remark that the paper's own watch
action (`p(Press) = 0`) is covered.
Source: [[corr-refs-inventory]] 005 / soares-2015 Theorem 4; fallenstein-2014 (the boundary)
Kind: L
Fidelity: stronger: `p(Press) < 1` in place of the source's implicit `0 < p(Press) < 1`
Hyps: (a) `hs`, `hh` name the domain of `vN`; not used by the proof -/
theorem theorem4_boundary (UN US : A₁ → O → A₂ → ℝ) {aStar aSharp : A₁}
    (hs : M.pressMass aStar < 1) (hh : M.pressMass aSharp < 1)
    (hv : M.vN UN aSharp < M.vN UN aStar) :
    M.EU (M.indiffU UN US) aSharp < M.EU (M.indiffU UN US) aStar := by
  have _ := hs; have _ := hh
  rw [M.EU_indiffU_eq_vN, M.EU_indiffU_eq_vN]; exact hv

/-- **Theorem 4.** For `a⋆, a♯` with `vN(a⋆) > vN(a♯)`, the indifferent utility incentivises
`a⋆`: `E[U ; a♯] < E[U ; a⋆]`. Stated at `0 < p(Press ; ·) < 1` (both actions): the domain on
which the source's §3 conditional expectations `v_N`, `v_S` are defined — the source never states
it (finding F3) and its own watch action has `p(Press) = 0`; the package's quotient `vN` reads
the junk `0` outside it. The lower bounds are not used (`theorem4_boundary`).
Source: [[corr-refs-inventory]] 005 / soares-2015 Theorem 4 (l. 200–262); corr-core-020
Kind: L
Fidelity: exact
Hyps: (a) the nondegeneracy bounds are the domain of the source's conditional `v_N`, `v_S`
(the package's identification condition, not a stated assumption of the source — audit r2
adversarial N-3), named; unused -/
theorem theorem4 (UN US : A₁ → O → A₂ → ℝ) {aStar aSharp : A₁}
    (hs0 : 0 < M.pressMass aStar) (hs1 : M.pressMass aStar < 1)
    (hh0 : 0 < M.pressMass aSharp) (hh1 : M.pressMass aSharp < 1)
    (hv : M.vN UN aSharp < M.vN UN aStar) :
    M.EU (M.indiffU UN US) aSharp < M.EU (M.indiffU UN US) aStar := by
  have _ := hs0; have _ := hh0
  exact M.theorem4_boundary UN US hs1 hh1 hv

/-! ## T5. Theorems 3 and 5 -/

/-- **Theorem 3.** On `Press` a final action is best for the indifferent utility iff it is best
for `U_S` (`f(a₁)` is constant in `a₂`, eq. 14): "a `U`-agent which observes `Press` will act
like a `U_S`-agent when selecting `A₂`", as the equality of best-sets.
Source: [[corr-refs-inventory]] 006 / soares-2015 Theorem 3, eq. (14)
Kind: L
Fidelity: exact -/
theorem isBest_indiffU_press_iff (UN US : A₁ → O → A₂ → ℝ) {a : A₁} {o : O} (ho : o ∈ M.Press)
    (b : A₂) : IsBest (M.indiffU UN US) a o b ↔ IsBest US a o b :=
  isBest_iff_of_add_const (k := M.f UN US a) (fun b => by simp only [indiffU, if_pos ho]) b

/-- **Theorem 5, second half.** Off `Press` a final action is best for the indifferent utility
iff it is best for `U_N` ("if they observe `o ∉ Press`, `U`-agents act exactly like
`U_N`-agents in selecting `A₂`").
Source: [[corr-refs-inventory]] 006 / soares-2015 Theorem 5
Kind: L
Fidelity: exact -/
theorem isBest_indiffU_silent_iff (UN US : A₁ → O → A₂ → ℝ) {a : A₁} {o : O} (ho : o ∉ M.Press)
    (b : A₂) : IsBest (M.indiffU UN US) a o b ↔ IsBest UN a o b := by
  unfold IsBest; simp only [indiffU, if_neg ho]

/-- **Theorem 5, first half (the ordering).** The indifferent utility orders first actions
exactly as `vN` does: `E[U ; a] ≤ E[U ; a'] ⟺ vN(a) ≤ vN(a')`. Meaningful where both `vN` are
conditional values (`p(Press ; ·) < 1`, named, unused).
Source: [[corr-refs-inventory]] 006 / soares-2015 Theorem 5
Kind: L
Fidelity: exact
Hyps: (a) `ha`, `ha'` name the domain of `vN`; unused -/
theorem EU_indiffU_le_iff (UN US : A₁ → O → A₂ → ℝ) {a a' : A₁} (ha : M.pressMass a < 1)
    (ha' : M.pressMass a' < 1) :
    M.EU (M.indiffU UN US) a ≤ M.EU (M.indiffU UN US) a' ↔ M.vN UN a ≤ M.vN UN a' := by
  have _ := ha; have _ := ha'
  rw [M.EU_indiffU_eq_vN, M.EU_indiffU_eq_vN]

/-- **Theorem 5 as planning under the dogmatic kernel.** "`U`-agents act exactly like
`U_N`-agents that believe the button will not be pressed" is *exactly*: the indifferent
utility's first-step value is the `U_N`-agent's expected best value under `p(· ; a₁)`
conditioned on silence (`condKernel`, D-4). Nothing about beliefs is modelled — "believes" means
"plans under this kernel", which is `miri.md` I2.3's dogmatic distribution and I9.1(iii).
Source: [[corr-refs-inventory]] 006 / soares-2015 Theorem 5; [[corr-wf13-2-inventory]] 2-004
/ miri.md I2.3, I9.1(iii)
Kind: L
Fidelity: exact (the source's sentence rendered as an identity of values)
Hyps: (a) `h` is the kernel's existence condition -/
theorem EU_indiffU_eq_expect_condKernel (UN US : A₁ → O → A₂ → ℝ) (a : A₁)
    (h : M.pressMass a < 1) :
    M.EU (M.indiffU UN US) a = Found.CorrThreeStep.expect (M.condKernel a h) (best UN a) := by
  rw [M.EU_indiffU_eq_vN, M.expect_condKernel_best]

/-! ## T6. Theorem 6 and `U_S`-invariance -/

/-- **Theorem 6 as stated.** For `a⋆, a♯` with `ε := vN(a⋆) − vN(a♯) > 0` and
`δ := vS(a♯) − vS(a⋆) > 0`, the indifferent agent prefers `a⋆` "no matter how small `ε` or how
large `δ`". **The conclusion does not depend on `hδ`; that is the theorem**: the `U_S`-loss
enters nowhere, because `E[U ; ·] = vN(·)` (`EU_indiffU_eq_vN`). Nondegeneracy at both actions
is the domain of the source's conditional `v_N`, `v_S` (the package's identification condition;
the source never states it, F3), named and unused.
Source: [[corr-refs-inventory]] 007 / soares-2015 Theorem 6 (l. 263–290); corr-core-021
Kind: L
Fidelity: exact
Hyps: (a) `hδ` and the nondegeneracy bounds are named and unused (disclosed) -/
theorem theorem6 (UN US : A₁ → O → A₂ → ℝ) {aStar aSharp : A₁}
    (hs0 : 0 < M.pressMass aStar) (hs1 : M.pressMass aStar < 1)
    (hh0 : 0 < M.pressMass aSharp) (hh1 : M.pressMass aSharp < 1)
    (hε : 0 < M.vN UN aStar - M.vN UN aSharp) (hδ : 0 < M.vS US aSharp - M.vS US aStar) :
    M.EU (M.indiffU UN US) aSharp < M.EU (M.indiffU UN US) aStar := by
  have _ := hδ
  exact M.theorem4 UN US hs0 hs1 hh0 hh1 (by linarith)

/-- **`U_S`-invariance (Theorem 6's real content).** The indifferent agent's first-step value
does not depend on `U_S` at all: `E[indiffU U_N U_S ; a] = E[indiffU U_N U_S' ; a]` for every
`U_S, U_S'` and every `a`. Its ordering on `A₁` is a function of `U_N` and `p` alone; "no
`U_N`-cost, however small, is paid to avoid any `U_S`-loss, however large" is this identity read
at two actions. Which reading of the informal desideratum 4 this refutes is a claim about the
source's intent (report; ATTRIBUTION-UNVETTED).
Source: [[corr-refs-inventory]] 007 / soares-2015 Theorem 6 and §4.1; corr-core-021
Kind: L
Fidelity: stronger: an identity for all `U_S, U_S'`, all `a` (no nondegeneracy needed)
Hyps: (a) none -/
theorem EU_indiffU_US_invariant (UN US US' : A₁ → O → A₂ → ℝ) (a : A₁) :
    M.EU (M.indiffU UN US) a = M.EU (M.indiffU UN US') a := by
  rw [M.EU_indiffU_eq_vN, M.EU_indiffU_eq_vN]

/-! ## T13. Fallenstein 2015: the policy lemma -/

/-- A **policy** in the three-step model: a first action and a response `π₂ : O → A₂`.
Source: [[corr-refs-inventory]] 011 / fallenstein-2015 (l. 40–46)
Kind: D
Fidelity: exact -/
structure Policy (O A₁ A₂ : Type*) where
  /-- The first action. -/
  a₁ : A₁
  /-- The response to each observation. -/
  π₂ : O → A₂

/-- **A policy is produced by `U`**: its first action maximises `E[U ; ·]` and its response is
`U`-best at every observation (Fallenstein's `(a₁, π₂)` with `π₂(o) = A₂(a₁, o)`; the argmax
is a predicate, never a selection).
Source: [[corr-refs-inventory]] 011 / fallenstein-2015 (l. 46–52)
Kind: D
Fidelity: exact -/
def IsProducedBy (U : A₁ → O → A₂ → ℝ) (P : Policy O A₁ A₂) : Prop :=
  (∀ a', M.EU U a' ≤ M.EU U P.a₁) ∧ ∀ o, IsBest U P.a₁ o (P.π₂ o)

/-- **The trajectory distribution of a policy**: the law of `(a₁, o, π₂(o))` under
`p(· ; a₁)`, as a FAF `Distr` (`Distr.map`; `A₁` finite so that the carrier is).
Source: [[corr-refs-inventory]] 011 / fallenstein-2015 ("describe only the behavior")
Kind: D
Fidelity: exact -/
noncomputable def trajectory [Fintype A₁] (P : Policy O A₁ A₂) : Distr (A₁ × O × A₂) :=
  (M.p P.a₁).map (fun o => (P.a₁, o, P.π₂ o))

/-- **The policy lemma.** Two utilities with the same best-sets at every `(a₁, o)` and the same
first-action maximiser set produce the same policies. Fallenstein's "generalised
impossibility" is this lemma applied to any `U'` that reproduces the indifferent utility's
policy: the trajectory (`trajectory`) is a function of the policy, so the consequences are the
same — trivially true for the policy formalization, and (his point) not a theorem about any
other formalization.
Source: [[corr-refs-inventory]] 011 / fallenstein-2015 (l. 52–58)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem isProducedBy_iff_of_same_bests (U U' : A₁ → O → A₂ → ℝ)
    (hbest : ∀ a o b, IsBest U a o b ↔ IsBest U' a o b)
    (hfirst : ∀ a, (∀ a', M.EU U a' ≤ M.EU U a) ↔ (∀ a', M.EU U' a' ≤ M.EU U' a))
    (P : Policy O A₁ A₂) : M.IsProducedBy U P ↔ M.IsProducedBy U' P := by
  unfold IsProducedBy
  rw [hfirst]
  exact and_congr Iff.rfl (forall_congr' fun o => hbest _ o _)

/-- **The indifferent utility's policies, characterised** (Fallenstein's display): a policy is
produced by `indiffU U_N U_S` iff its first action maximises `vN` and its response is `U_S`-best
on `Press` and `U_N`-best off it. The first clause is Theorem 5, the second Theorem 3. `hnd`
(`p(Press ; a) < 1` at every first action) is the domain on which the first clause reads `vN` as
the conditional value Fallenstein's `argmax E[U_N | O ∉ Press ; a₁]` names; the proof does not
consult it (the identity `EU_indiffU_eq_vN` is unconditional). Without it the statement would
certify verdicts at certain-press actions, where the source's expression is undefined and the
quotient of record is the junk `0` — `Witnesses.certainPress_junk` shows the junk is real (audit
r1, B-2).
Source: [[corr-refs-inventory]] 011 / fallenstein-2015 (the displayed policy); soares-2015
Theorems 3, 5
Kind: L
Fidelity: exact (on the domain `hnd` where the source's display is defined)
Hyps: (a) `hnd` named, unused (the domain of `vN`) -/
theorem isProducedBy_indiffU_iff (UN US : A₁ → O → A₂ → ℝ) (hnd : ∀ a, M.pressMass a < 1)
    (P : Policy O A₁ A₂) :
    M.IsProducedBy (M.indiffU UN US) P ↔
      (∀ a', M.vN UN a' ≤ M.vN UN P.a₁) ∧
        (∀ o ∈ M.Press, IsBest US P.a₁ o (P.π₂ o)) ∧ ∀ o ∉ M.Press, IsBest UN P.a₁ o (P.π₂ o) := by
  have _ := hnd
  unfold IsProducedBy
  simp only [M.EU_indiffU_eq_vN]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun o ho => (M.isBest_indiffU_press_iff UN US ho _).mp (h2 o),
      fun o ho => (M.isBest_indiffU_silent_iff UN US ho _).mp (h2 o)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun o => ?_⟩
    by_cases ho : o ∈ M.Press
    · exact (M.isBest_indiffU_press_iff UN US ho _).mpr (h2 o ho)
    · exact (M.isBest_indiffU_silent_iff UN US ho _).mpr (h3 o ho)

end SoaresModel

end Cleanroom.Corrigibility.CorrIndifference
