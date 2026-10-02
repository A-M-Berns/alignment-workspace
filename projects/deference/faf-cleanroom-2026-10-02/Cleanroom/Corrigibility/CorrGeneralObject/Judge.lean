import Cleanroom.Corrigibility.CorrGeneralObject.Endorse

/-!
# corr-general-object — T12: the legitimacy judge is `P_t`; T13: self-observation fixed points

Carrier `Ω = W × I`: a world and "which of finitely many credences I will hold" (the
`pushJoint` of `corr-reflect-frames`). The meta-proposition `B_i = {(w, j) | j = i}`.

* **T12(a) D.** The legitimacy judgment of the transition to `ρ i` is `postPush` for the kernel
  `K · i` — `judgeTransition` — no separate object (outline l. 42, resolved 1b: "`P_t`'s
  conditionals on future-total-state events are its legitimacy judgments").
* **T12(b) N+.** The (ii) clause, "no outside view": a toy where `P_t` does not endorse the
  transition to `ρ` (`postPush ≠ ρ` by a wide margin) while `ρ` itself gives the same event
  probability one (`judge_no_outside_view`) — judged illegitimate only by the past self.
* **T12(c) T.** Reversal under a physics-delivered `Q` is judged under `Q`: a self-endorsing `Q`
  never reverts (`no_revert_of_isOptimal`).
* **T13(a) L.** The fixed-point condition "`Q(B_i) = 1` and `Q(· | B_i) = Q`" has a redundant
  clause: the second follows from the first (`isFixedPointAt_iff`) — a finding against Stmt 14.
* **T13(b) N+.** A landed non-fixed-point `Q` with a tampering hypothesis acts on
  `Q' = Q(· | B_i) ≠ Q`, and the optimal action differs (`landed_update_flips`).
* **T13(c)**, A5's reading "a legitimizing installation lands fixed points": the exact statement
  is an **iff** (repair round 1) — for an endorsed pair of positive push mass, the target is a
  fixed point at `i` iff the kernel vanishes at every `P`-positive world outside `B_i`
  (`fixedPoint_iff_kernel_supported_of_endorsed`; mass form
  `fixedPoint_iff_offMass_eq_zero_of_endorsed`). Hence **proved** when the push event lies inside
  the meta-proposition (`fixedPoint_of_endorsed_supported` — D5's identification
  `E_Q = {P_{t+1} = Q}`; instance `j12_fixedPoint_instance`: the hard push `𝟙_{B_1}` from the
  uniform prior endorses its own posterior, which is a fixed point), and **refuted** for a general
  endorsing kernel (`not_fixedPoint_of_endorsed_general`: the certain kernel, push mass `1`,
  endorses `P` itself, which need not be introspective; instance `j12_not_fixedPoint`).

The general existence question is `corr-reflect-frames`' OPEN `universalSelfRefSpace_exists_open`
(cited, not restated).

Sources: [[corrigibility-discussion-outline]] l. 42 (1b resolved); [[d1-special-case-final]] S11;
[[anticipatory-final]] Stmt 14, A5; [[corr-core-inventory]] 017; [[corr-wf14b-inventory]] 026, 043.
-/

namespace Cleanroom.Corrigibility.CorrGeneralObject

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

noncomputable section

set_option linter.unusedSectionVars false

variable {W I : Type} [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]

/-! ## T12: the judge -/

/-- **The legitimacy judgment of a transition is `P_t`'s conditional on the push event** —
`postPush` for the kernel `K · i` of the announcement `i`. No separate object (resolved 1b).
Source: [[corrigibility-discussion-outline]] l. 42; [[corr-core-inventory]] 017
Kind: D
Fidelity: exact (finite self-referential carrier `W × I`) -/
def judgeTransition (P : Distr (W × I)) (K : W × I → I → ℝ) (hK : ∀ x i, 0 ≤ K x i) (i : I)
    (h : 0 < pushMass P (fun x => K x i)) : Distr (W × I) :=
  postPush P (fun x => K x i) (fun x => hK x i) h

/-- The meta-proposition `B_i = {(w, j) | j = i}`: "I will hold credence `i`".
Source: [[anticipatory-final]] Stmt 14 (`B_Q`); [[corr-wf14b-inventory]] 026
Kind: D
Fidelity: exact -/
def metaProp (i : I) : Finset (W × I) := univ.filter (fun x => x.2 = i)

/-- Membership in the meta-proposition. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem mem_metaProp (i : I) (x : W × I) : x ∈ (metaProp i : Finset (W × I)) ↔ x.2 = i := by
  simp [metaProp]

/-- **T12(c): a self-endorsing `Q` never reverts** — reversal under a physics-delivered `Q` is
judged under `Q`, and `E_Q[V revert] ≤ E_Q[V stay]` whenever `stay = πQ` (kind T: the definition
of `πQ`; the content is the witness (b)).
Source: [[d1-special-case-final]] S11; [[corr-wf14b-inventory]] 043
Kind: T
Fidelity: exact -/
theorem no_revert_of_isOptimal {Ω A : Type} [Fintype Ω] [Fintype A] (Q : Distr Ω) (V : A → Ω → ℝ)
    {stay : A} (hstay : IsOptimal Q V stay) (revert : A) :
    expect Q (V revert) ≤ expect Q (V stay) := hstay revert

/-! ## T13: fixed points -/

/-- `Q` is a **fixed point at `i`**: `Q(B_i) = 1` and `Q(· | B_i) = Q` (product form).
Source: [[anticipatory-final]] Stmt 14, A5
Kind: D
Fidelity: exact (both clauses, as the source states them; `isFixedPointAt_iff` shows the second
is redundant) -/
def IsFixedPointAt (Q : Distr (W × I)) (i : I) : Prop :=
  (∑ x ∈ metaProp i, Q.mass x = 1) ∧
    ∀ x, Q.mass x * (∑ x' ∈ metaProp i, Q.mass x') = ind (metaProp i) x * Q.mass x

/-- **T13(a): `Q(B_i) = 1` already gives `Q(· | B_i) = Q`** — the second clause of Stmt 14's
fixed-point condition is redundant (a finding).
Source: [[anticipatory-final]] Stmt 14; mandate T13(a)
Kind: L
Fidelity: exact -/
theorem isFixedPointAt_iff (Q : Distr (W × I)) (i : I) :
    IsFixedPointAt Q i ↔ ∑ x ∈ metaProp i, Q.mass x = 1 := by
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, fun x => ?_⟩
    rw [h, mul_one]
    unfold ind Cleanroom.Found.LitDdbFrames.ind
    by_cases hx : x ∈ (metaProp i : Finset (W × I))
    · simp [hx]
    · have hcompl : ∑ x' ∈ (metaProp i : Finset (W × I))ᶜ, Q.mass x' = 0 := by
        have := sum_add_sum_compl (metaProp i : Finset (W × I)) Q.mass
        rw [h, Q.sum_eq_one] at this; linarith
      have : Q.mass x = 0 :=
        (sum_eq_zero_iff_of_nonneg fun x' _ => Q.nonneg x').1 hcompl x (mem_compl.2 hx)
      simp [hx, this]

/-- **T13(c), the exact statement (mass form)**: for an endorsed pair of positive push mass, `Q`
is a fixed point at `i` **iff** the push carries no `P`-mass outside `B_i`:
`∑_{x ∉ B_i} P x · k x = 0`. Under endorsement `Q = postPush`, so
`Q(B_i) = P(E_Q ∧ B_i) / P(E_Q)`, which is `1` iff the off-`B_i` push mass vanishes.
Source: [[anticipatory-final]] A5, l. 132; mandate T13(c); audit r1 fidelity 3.5 (the necessity
direction the first round left unproved)
Kind: L
Fidelity: exact (both directions)
Hyps: (a) the guard, `Endorsed` -/
theorem fixedPoint_iff_offMass_eq_zero_of_endorsed (P Q : Distr (W × I)) {k : W × I → ℝ}
    (hk : ∀ x, 0 ≤ k x) (h : 0 < pushMass P k) (i : I) (hE : Endorsed P k Q) :
    IsFixedPointAt Q i ↔ ∑ x ∈ (metaProp i : Finset (W × I))ᶜ, P.mass x * k x = 0 := by
  rw [isFixedPointAt_iff, ← (endorsed_iff_postPush_eq P hk h Q).1 hE]
  simp only [postPush_mass]
  rw [← sum_div, div_eq_one_iff_eq h.ne']
  have hsplit : ∑ x ∈ (metaProp i : Finset (W × I)), P.mass x * k x +
      ∑ x ∈ (metaProp i : Finset (W × I))ᶜ, P.mass x * k x = ∑ x, P.mass x * k x :=
    sum_add_sum_compl _ _
  unfold pushMass
  constructor
  · intro heq; linarith
  · intro hz; linarith

/-- **T13(c), the exact statement (kernel form)**: for an endorsed pair of positive push mass,
`Q` is a fixed point at `i` **iff** the kernel vanishes at every `P`-positive world outside
`B_i` — "the push event lies inside `B_i`", D5's identification of the push event with "I will
hold `ρ_i`" (ATTRIBUTION-UNVETTED: Eisenstat via Abram), read as a condition on the kernel.
Source: [[anticipatory-final]] A5 ("a legitimizing installation is one that lands fixed
points"), l. 132; mandate T13(c); audit r1 fidelity 3.5
Kind: L
Fidelity: exact (both directions; A5's sentence is the `⇐`)
Hyps: (a) the guard, `Endorsed` -/
theorem fixedPoint_iff_kernel_supported_of_endorsed (P Q : Distr (W × I)) {k : W × I → ℝ}
    (hk : ∀ x, 0 ≤ k x) (h : 0 < pushMass P k) (i : I) (hE : Endorsed P k Q) :
    IsFixedPointAt Q i ↔
      ∀ x, x ∉ (metaProp i : Finset (W × I)) → 0 < P.mass x → k x = 0 := by
  rw [fixedPoint_iff_offMass_eq_zero_of_endorsed P Q hk h i hE,
    sum_eq_zero_iff_of_nonneg (fun x _ => mul_nonneg (P.nonneg x) (hk x))]
  constructor
  · intro hz x hx hP
    rcases mul_eq_zero.1 (hz x (mem_compl.2 hx)) with h0 | h0
    · exact absurd h0 hP.ne'
    · exact h0
  · intro hs x hx
    rcases (P.nonneg x).eq_or_lt with h0 | h0
    · rw [← h0, zero_mul]
    · rw [hs x (mem_compl.1 hx) h0, mul_zero]

/-- **T13(c), the provable half** (now a corollary of the iff): an endorsed target of a push
whose kernel is supported inside the meta-proposition `B_i` is a fixed point at `i`.
Source: [[anticipatory-final]] Stmt 14, A5 ("a legitimizing installation is one that lands fixed
points"); mandate T13(c)
Kind: L
Fidelity: variant: with the support hypothesis on the kernel (without it the claim is false,
`not_fixedPoint_of_endorsed_general`); the exact form is `fixedPoint_iff_kernel_supported_of_endorsed`
Hyps: (a) the guard, `Endorsed`, the support hypothesis -/
theorem fixedPoint_of_endorsed_supported (P Q : Distr (W × I)) {k : W × I → ℝ}
    (hk : ∀ x, 0 ≤ k x) (h : 0 < pushMass P k) {i : I}
    (hsupp : ∀ x, x ∉ (metaProp i : Finset (W × I)) → k x = 0) (hE : Endorsed P k Q) :
    IsFixedPointAt Q i :=
  (fixedPoint_iff_kernel_supported_of_endorsed P Q hk h i hE).2 fun x hx _ => hsupp x hx

/-- **T13(c), the refuting half**: the certain kernel `k ≡ 1` endorses `P` itself (push mass `1`),
so "endorsed ⟹ fixed point" would make every prior a fixed point at every `i` — false whenever
`P(B_i) < 1`. The refutation is by the *uninformative* push (the certain kernel, which no reading
of A5's "legitimizing installation" covers): it refutes the mandate's unrestricted phrasing
("`Endorsed P k Q → Q(B_i) = 1` over an arbitrary kernel"), not A5's own sentence, which is
stated on the event `⌜I now believe Q⌝ = B_Q` and is the `⇐` of
`fixedPoint_iff_kernel_supported_of_endorsed`.
Source: mandate T13(c) ("the answer is likely refute"); [[anticipatory-final]] A5
Kind: P
Fidelity: exact (refutation of the mandate's unrestricted implication)
Hyps: (a) `P(B_i) < 1` -/
theorem not_fixedPoint_of_endorsed_general (P : Distr (W × I)) {i : I}
    (hlt : ∑ x ∈ metaProp i, P.mass x < 1) :
    Endorsed P (fun _ => (1 : ℝ)) P ∧ 0 < pushMass P (fun _ => (1 : ℝ)) ∧ ¬ IsFixedPointAt P i := by
  have hm : pushMass P (fun _ => (1 : ℝ)) = 1 := by unfold pushMass; simp [P.sum_eq_one]
  refine ⟨fun x => by rw [hm]; ring, by rw [hm]; exact one_pos, ?_⟩
  rw [isFixedPointAt_iff]
  exact hlt.ne

/-! ## Witnesses on `Fin 2 × Fin 2` -/

/-- Sums over `Fin 2 × Fin 2` expand to four terms. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem sum_fin2_prod (f : Fin 2 × Fin 2 → ℝ) :
    ∑ x, f x = f (0, 0) + f (0, 1) + f (1, 0) + f (1, 1) := by
  rw [Fintype.sum_prod_type]
  simp [Fin.sum_univ_two]; ring

/-- The uniform prior on `Fin 2 × Fin 2`. Source: mandate T12(b) witness. Kind: D. Fidelity: exact -/
def j12P : Distr (Fin 2 × Fin 2) where
  mass _ := 1/4
  nonneg _ := by norm_num
  sum_eq_one := by rw [sum_fin2_prod]; norm_num

/-- The announced credence `ρ₁ = δ_{(0,1)}`, supported in `B_1`. Source: mandate T12(b) witness. Kind: D. Fidelity: exact -/
def j12ρ : Distr (Fin 2 × Fin 2) where
  mass x := if x = (0, 1) then 1 else 0
  nonneg x := by split_ifs <;> norm_num
  sum_eq_one := by rw [sum_fin2_prod]; simp

/-- The hard push `𝟙_{B_1}` has mass `1/2` under the uniform prior. Source: none: infrastructure.
Kind: L. Fidelity: n/a -/
theorem j12_pushMass_B1 : pushMass j12P (ind (metaProp 1)) = 1/2 := by
  have hB : (metaProp 1 : Finset (Fin 2 × Fin 2)) = {(0, 1), (1, 1)} := by decide
  rw [pushMass_ind, hB, sum_pair (by decide)]; simp [j12P]; norm_num

/-- The positivity guard for `𝟙_{B_1}` under the uniform prior. Source: none: infrastructure.
Kind: L. Fidelity: n/a -/
theorem j12_pushMass_B1_pos : 0 < pushMass j12P (ind (metaProp 1)) := by
  rw [j12_pushMass_B1]; norm_num

/-- **N+ for T12(b), "no outside view"**: the past self `P_t` (uniform) judges the transition to
`ρ₁` by `P_t(· | B_1) = (0, 0, 1/2, 1/2) ≠ ρ₁` — not endorsed — while `ρ₁` itself gives `B_1`
probability one: the transition is judged illegitimate only by the past self.
Source: [[corrigibility-discussion-outline]] l. 42 (ii); [[d1-special-case-final]] S11
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem judge_no_outside_view :
    0 < pushMass j12P (ind (metaProp 1)) ∧
      ¬ Endorsed j12P (ind (metaProp 1)) j12ρ ∧
      (∑ x ∈ (metaProp 1 : Finset (Fin 2 × Fin 2)), j12ρ.mass x = 1) ∧
      (postPush j12P (ind (metaProp 1)) (isKernel_ind _).nonneg j12_pushMass_B1_pos).mass (1, 1)
        = 1/2 := by
  have hB : (metaProp 1 : Finset (Fin 2 × Fin 2)) = {(0, 1), (1, 1)} := by decide
  have hm := j12_pushMass_B1
  refine ⟨j12_pushMass_B1_pos, ?_, ?_, ?_⟩
  · intro h
    have := h (1, 1)
    rw [hm] at this
    simp [j12P, j12ρ, ind, Cleanroom.Found.LitDdbFrames.ind, hB] at this <;> norm_num at this
  · rw [hB, sum_pair (by decide)]; simp [j12ρ]
  · rw [postPush_mass, hm]
    simp [j12P, ind, Cleanroom.Found.LitDdbFrames.ind, hB] <;> norm_num

/-- T13(b)'s landed credence `Q = (1/2, 1/4, 0, 1/4)` on `(w, i)` in the order
`(0,0), (0,1), (1,0), (1,1)`: `Q(B_1) = 1/2`, and the tampering hypothesis `T = {w = 1}` has
`Q(T) = 1/4` but `Q(T | B_1) = 1/2`. Source: mandate T13(b) witness. Kind: D. Fidelity: exact -/
def j13Q : Distr (Fin 2 × Fin 2) where
  mass x := if x = (0, 0) then 1/2 else if x = (1, 0) then 0 else 1/4
  nonneg x := by split_ifs <;> norm_num
  sum_eq_one := by rw [sum_fin2_prod]; simp; norm_num

/-- T13(b)'s menu: `a` (proceed) pays `1` if `w = 0` and `−2` if `w = 1`; `b` (cautious) pays `0`.
Source: mandate T13(b) witness. Kind: D. Fidelity: exact -/
def j13V : Bool → Fin 2 × Fin 2 → ℝ := fun a x => if a then (if x.1 = 0 then 1 else -2) else 0

/-- `B_1` on `Fin 2 × Fin 2` is `{(0,1), (1,1)}`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem j13_metaProp : (metaProp 1 : Finset (Fin 2 × Fin 2)) = {(0, 1), (1, 1)} := by decide

/-- `Q(B_1) = 1/2` for the T13(b) witness. Source: mandate T13(b) witness. Kind: L. Fidelity: exact -/
theorem j13_mass_B : ∑ x ∈ (metaProp 1 : Finset (Fin 2 × Fin 2)), j13Q.mass x = 1/2 := by
  rw [j13_metaProp, sum_pair (by decide)]; simp [j13Q]; norm_num

/-- The positivity guard for the landed update: the hard push `𝟙_{B_1}` has mass `1/2`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem j13_pushMass_pos : 0 < pushMass j13Q (ind (metaProp 1)) := by
  rw [pushMass_ind, j13_mass_B]; norm_num

/-- **N+ for T13(b)**: `Q` is not a fixed point (`Q(B_1) = 1/2`), the tampering hypothesis is
raised by observing `B_1` (`Q(T ∧ B_1) · 1 > Q(T) · Q(B_1)`: `1/4 > 1/8`), the landed agent acts on
`Q' = Q(· | B_1) ≠ Q`, and the optimal action flips: `a` is `Q`-optimal, `b` is `Q'`-optimal
and `a` is not.
Source: [[anticipatory-final]] Stmt 14 ("a successor whose meta-beliefs say 'states like this are
usually the product of tampering' discounts its landed state"); mandate T13(b)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem landed_update_flips :
    (∑ x ∈ (metaProp 1 : Finset (Fin 2 × Fin 2)), j13Q.mass x = 1/2) ∧
      ¬ IsFixedPointAt j13Q 1 ∧
      (j13Q.mass (1, 1) * 1 > (j13Q.mass (1, 0) + j13Q.mass (1, 1)) * (1/2)) ∧
      IsOptimal j13Q j13V true ∧
      IsOptimal (postPush j13Q (ind (metaProp 1)) (isKernel_ind _).nonneg j13_pushMass_pos)
        j13V false ∧
      ¬ IsOptimal (postPush j13Q (ind (metaProp 1)) (isKernel_ind _).nonneg j13_pushMass_pos)
        j13V true := by
  have hB := j13_metaProp
  have hmass := j13_mass_B
  have hm : pushMass j13Q (ind (metaProp 1)) = 1/2 := by rw [pushMass_ind, hmass]
  refine ⟨hmass, ?_, ?_, ?_, ?_, ?_⟩
  · rw [isFixedPointAt_iff, hmass]; norm_num
  · simp [j13Q]; norm_num
  · intro b; cases b <;> simp [expect, j13Q, j13V, sum_fin2_prod] <;> norm_num
  · intro b
    unfold expect
    simp only [postPush_mass, hm]
    cases b <;> simp [j13Q, j13V, sum_fin2_prod, ind, Cleanroom.Found.LitDdbFrames.ind, hB] <;>
      norm_num
  · intro hopt
    have := hopt false
    unfold expect at this
    simp only [postPush_mass, hm] at this
    simp [j13Q, j13V, sum_fin2_prod, ind, Cleanroom.Found.LitDdbFrames.ind, hB] at this <;>
      norm_num at this

/-- **N+ for T13(c)'s refutation**: on the uniform prior `P(B_1) = 1/2 < 1`.
Source: mandate T13(c)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem j12_not_fixedPoint : ¬ IsFixedPointAt j12P 1 := by
  have hB : (metaProp 1 : Finset (Fin 2 × Fin 2)) = {(0, 1), (1, 1)} := by decide
  exact (not_fixedPoint_of_endorsed_general j12P (i := 1)
    (by rw [hB, sum_pair (by decide)]; simp [j12P]; norm_num)).2.2

/-- **N+ for T13(c)'s `⇐`** (the iff applied to a concrete endorsed pair): the hard push `𝟙_{B_1}`
from the uniform prior (mass `1/2`) endorses its own post-push credence `(0, 0, 1/2, 1/2)`
(`endorsed_iff_postPush_eq`), its kernel vanishes off `B_1`, and
`fixedPoint_iff_kernel_supported_of_endorsed` delivers `IsFixedPointAt (postPush …) 1` — A5's
sentence under D5's identification, instantiated. Nothing degenerate: four worlds, `B_1` half of
them, the target is not a Dirac.
Source: [[anticipatory-final]] A5, l. 132; audit r2 fidelity 3.2 (`audit-r2-probes/FixedPointInstance.lean`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem j12_fixedPoint_instance :
    Endorsed j12P (ind (metaProp 1))
        (postPush j12P (ind (metaProp 1)) (isKernel_ind _).nonneg j12_pushMass_B1_pos) ∧
      (∀ x, x ∉ (metaProp 1 : Finset (Fin 2 × Fin 2)) → 0 < j12P.mass x → ind (metaProp 1) x = 0) ∧
      IsFixedPointAt (postPush j12P (ind (metaProp 1)) (isKernel_ind _).nonneg j12_pushMass_B1_pos) 1 ∧
      (postPush j12P (ind (metaProp 1)) (isKernel_ind _).nonneg j12_pushMass_B1_pos).mass (1, 1)
        = 1/2 := by
  have hE : Endorsed j12P (ind (metaProp 1))
      (postPush j12P (ind (metaProp 1)) (isKernel_ind _).nonneg j12_pushMass_B1_pos) :=
    (endorsed_iff_postPush_eq j12P (isKernel_ind _).nonneg j12_pushMass_B1_pos _).2 rfl
  have hsupp : ∀ x, x ∉ (metaProp 1 : Finset (Fin 2 × Fin 2)) → 0 < j12P.mass x →
      ind (metaProp 1) x = 0 := by
    intro x hx _
    simp [ind, Cleanroom.Found.LitDdbFrames.ind, hx]
  refine ⟨hE, hsupp, ?_, judge_no_outside_view.2.2.2⟩
  exact (fixedPoint_iff_kernel_supported_of_endorsed j12P _ (isKernel_ind _).nonneg
    j12_pushMass_B1_pos 1 hE).2 hsupp

end

end Cleanroom.Corrigibility.CorrGeneralObject
