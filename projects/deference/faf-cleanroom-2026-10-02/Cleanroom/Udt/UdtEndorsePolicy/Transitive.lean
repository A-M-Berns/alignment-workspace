import Cleanroom.Udt.UdtEndorsePolicy.Defs
import Mathlib.Logic.Relation
import Mathlib.Order.RelClasses
import Mathlib.Data.ZMod.Defs

/-!
# T6: is conditional endorsement transitive? (the extension of record)

Source: [[meaning-and-agency-reference]] §Conditional Endorsement and Q1: "How well can we use
conditional endorsement to characterize optimization power (or more generally, level of
endorsement)? Is it transitive?"; udt-rep-2-015; trust-lab-070 / scout Q4.

**Setting (belief form, finite frame).** A target event `X`, a family of belief reports
`V : ι → Ω → ℝ`, and the relation `CondR w X V i j := CondBeliefEndorses w X (V j) (V i)`
("`V i` is endorsed given `V j`": `P(X | V j = x, V i = y) = y` on every positive pair). The
post's "trusts more" is `Prec i j := CondR i j ∧ ¬ CondR j i`.

**Answers.**
* `condR_self_iff` (L): `CondR i i` is unconditional belief endorsement of `V i`.
* **Not transitive** (`TransitiveWitness.lean`, `condEndorse_not_transitive`, N+): an
  eight-point frame with three non-constant reports has `CondR i j`, `CondR j k`, `¬ CondR i k`;
  the same frame has `Prec i j`, `Prec j k`, `¬ Prec i k`, so `Prec` is not a strict partial
  order.
* **Acyclic** (`condEndorse_acyclic`, P): `CondR i j ∧ CondR j k ∧ CondR k i` forces
  `V i = V j = V k` on the support. Engine: `CondR i j` with `V j` calibrated gives
  `E[V i²] − E[V j²] = E[(V i − V j)²] ≥ 0` (`m2_sub_eq`), and the three differences telescope
  around the cycle.
* **The surviving order** (`strictOrder_of_closure`, P): the transitive closure `Prec⁺` is a
  strict partial order (irreflexive, transitive), with no calibration hypothesis — every index
  on a `Prec`-cycle is the first index of some step and is therefore calibrated. The second
  moment `E[V²]` is a strict "resolution" potential along `Prec` among calibrated reports
  (`m2_le_of_condR`, `eq_on_support_of_condR_of_m2_eq`).

None of this settles "optimization power": the post's Q1 asks for a characterization, and what is
proved is the order-theoretic shape of the belief-form relation on finite frames.
-/

namespace Cleanroom.Udt.UdtEndorsePolicy

open Cleanroom.Udt.UdtPolicyCalc Finset

noncomputable section

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {ι : Type}

/-- **Endorsed-given**: `CondR w X V i j` iff `V i` is conditionally belief-endorsed given `V j`
(the post's "`P₁` endorses `W` given `V`" with `W := V i`, `V := V j`, belief form).
Source: [[meaning-and-agency-reference]] §Conditional Endorsement, Q1 | udt-rep-2-015 | trust-lab-070
Kind: D
Fidelity: variant: belief form on a finite frame; reports are random variables in `P₁`'s algebra (the post's quotation marks); positive-mass guard (ATTRIBUTION-UNVETTED)
Scope: finite `Ω`, positive-mass conditioning only; FAF-free
Hyps: n/a -/
def CondR (w : Ω → ℝ) (X : Finset Ω) (V : ι → Ω → ℝ) (i j : ι) : Prop :=
  CondBeliefEndorses w X (V j) (V i)

/-- **Strictly more trusted**: `Prec w X V i j` iff `V i` is endorsed given `V j` but not
conversely (the post's Alice/Bob/Carol example: "she continues to endorse Carol even after
learning Bob's decision; the reverse is not the case").
Source: [[meaning-and-agency-reference]] §Conditional Endorsement | udt-rep-2-015
Kind: D
Fidelity: variant: belief form
Hyps: n/a -/
def Prec (w : Ω → ℝ) (X : Finset Ω) (V : ι → Ω → ℝ) (i j : ι) : Prop :=
  CondR w X V i j ∧ ¬ CondR w X V j i

/-- The **second moment** `E[Q²]` of a report (the resolution potential).
Source: mandate T6(d)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def m2 (w Q : Ω → ℝ) : ℝ := wsum w (fun ω => Q ω ^ 2) univ

/-! ### (a) Reflexivity in the post's sense -/

/-- **`CondR i i` is unconditional belief endorsement of `V i`**: conditioning on `V i = x` and
`V i = y` is conditioning on `V i = x` (positive pairs have `x = y`).
Source: [[meaning-and-agency-reference]] §Conditional Endorsement | udt-rep-2-015 (T6(a))
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem condR_self_iff {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (X : Finset Ω) (V : ι → Ω → ℝ) (i : ι) :
    CondR w X V i i ↔ BeliefEndorses w X (V i) := by
  constructor
  · exact beliefEndorses_of_condBeliefEndorses hw
  · intro h x y hxy
    obtain ⟨ω, hωE, _⟩ := exists_pos_of_mass_pos hw hxy
    have hxyω : V i ω = x ∧ V i ω = y := by simpa using hωE
    have hxy' : x = y := hxyω.1.symm.trans hxyω.2
    subst hxy'
    have hcls : cls2 (V i) x (V i) x = cls (V i) x := by ext ω; simp
    rw [hcls] at hxy ⊢
    exact h x hxy

/-! ### The engine: `CondR i j` and a calibrated `V j` make `E[V i²] − E[V j²] = E[(V i − V j)²]` -/

omit [Fintype Ω] [DecidableEq Ω] in
/-- Supporting lemma: `wsum` respects pointwise equality on the event.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem wsum_congr_on {w f g : Ω → ℝ} {E : Finset Ω} (h : ∀ ω ∈ E, f ω = g ω) :
    wsum w f E = wsum w g E :=
  Finset.sum_congr rfl fun ω hω => by rw [h ω hω]

omit [DecidableEq Ω] in
/-- Supporting lemma: on the class `{Q = x}`, the factor `Q` is the constant `x`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem wsum_mul_cls (w Q f : Ω → ℝ) (x : ℝ) :
    wsum w (fun ω => Q ω * f ω) (cls Q x) = x * wsum w f (cls Q x) := by
  rw [← wsum_smul]
  exact wsum_congr_on fun ω hω => by rw [show Q ω = x by simpa using hω]

/-- **The cross moment collapses**: if `V i` is endorsed given `V j` and `V j` is calibrated
(unconditionally endorsed), then `E[V j · V i] = E[V j²]` — on each class `{V j = x}`,
`∑ w · V i = ∑ w · 1_X = x · P(V j = x) = ∑ w · V j`.
Source: mandate T6(c) (proof shape)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cross_eq_of_condR {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) {X : Finset Ω} {V : ι → Ω → ℝ}
    {i j : ι} (hij : CondR w X V i j) (hj : BeliefEndorses w X (V j)) :
    wsum w (fun ω => V j ω * V i ω) univ = wsum w (fun ω => V j ω * V j ω) univ := by
  refine wsum_eq_of_fibres hw _ _ univ (V j) fun x hx => ?_
  have hcls : (univ.filter fun ω => V j ω = x) = cls (V j) x := rfl
  rw [hcls] at hx ⊢
  rw [wsum_mul_cls, wsum_mul_cls]
  congr 1
  rw [← condBeliefEndorses_class_eq hw hij x, ← mass_inter_eq_wsum_ind, hj x hx,
    wsum_const_on (c := x) (fun ω hω => by simpa using hω)]

/-- **`E[V i²] − E[V j²] = E[(V i − V j)²]`** whenever `V i` is endorsed given `V j` and `V j` is
calibrated.
Source: mandate T6(c)/(d)
Kind: P
Fidelity: n/a (engine)
Hyps: (a) all -/
theorem m2_sub_eq {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) {X : Finset Ω} {V : ι → Ω → ℝ} {i j : ι}
    (hij : CondR w X V i j) (hj : BeliefEndorses w X (V j)) :
    m2 w (V i) - m2 w (V j) = wsum w (fun ω => (V i ω - V j ω) ^ 2) univ := by
  have hc := cross_eq_of_condR hw hij hj
  have e : wsum w (fun ω => (V i ω - V j ω) ^ 2) univ =
      wsum w (fun ω => V i ω ^ 2) univ - 2 * wsum w (fun ω => V j ω * V i ω) univ +
        wsum w (fun ω => V j ω * V j ω) univ := by
    simp only [wsum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ω _ => by ring
  rw [e, hc]
  unfold m2
  have : wsum w (fun ω => V j ω * V j ω) univ = wsum w (fun ω => V j ω ^ 2) univ :=
    wsum_congr_on fun ω _ => by ring
  rw [this]
  ring

omit [Fintype Ω] [DecidableEq Ω] in
/-- Supporting lemma: a weighted sum of squares is non-negative.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem wsum_sq_nonneg {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (f : Ω → ℝ) (E : Finset Ω) :
    0 ≤ wsum w (fun ω => f ω ^ 2) E :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (hw ω) (sq_nonneg _)

omit [DecidableEq Ω] in
/-- Supporting lemma: a vanishing weighted sum of squares vanishes on the support.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem eq_zero_on_support_of_wsum_sq_eq_zero {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) {f : Ω → ℝ}
    (h : wsum w (fun ω => f ω ^ 2) univ = 0) : ∀ ω, 0 < w ω → f ω = 0 := by
  intro ω hω
  have := (Finset.sum_eq_zero_iff_of_nonneg fun ω _ => mul_nonneg (hw ω) (sq_nonneg (f ω))).1 h
    ω (mem_univ ω)
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 hω.ne'
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0

/-! ### (d) The resolution order -/

/-- **Endorsed-given is compatible with the second moment**: `CondR i j` with `V j` calibrated
gives `E[V j²] ≤ E[V i²]` (a report endorsed given another is at least as resolved).
Source: mandate T6(d)
Kind: P
Fidelity: n/a (surviving neighbour of transitivity)
Hyps: (a) all; `hj` is the calibration of the conditioning report (needed: an uncalibrated constant `V j = c` with `V i = 1_X` has `CondR i j` and `E[V j²] = c²` unconstrained) -/
theorem m2_le_of_condR {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) {X : Finset Ω} {V : ι → Ω → ℝ} {i j : ι}
    (hij : CondR w X V i j) (hj : BeliefEndorses w X (V j)) : m2 w (V j) ≤ m2 w (V i) := by
  have := m2_sub_eq hw hij hj
  have := wsum_sq_nonneg hw (fun ω => V i ω - V j ω) univ
  linarith

/-- **Equal second moments force equal reports on the support** under `CondR i j` and a
calibrated `V j`.
Source: mandate T6(d)
Kind: P
Fidelity: n/a
Hyps: (a) all -/
theorem eq_on_support_of_condR_of_m2_eq {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) {X : Finset Ω}
    {V : ι → Ω → ℝ} {i j : ι} (hij : CondR w X V i j) (hj : BeliefEndorses w X (V j))
    (heq : m2 w (V i) = m2 w (V j)) : ∀ ω, 0 < w ω → V i ω = V j ω := by
  intro ω hω
  have h0 : wsum w (fun ω => (V i ω - V j ω) ^ 2) univ = 0 := by
    rw [← m2_sub_eq hw hij hj, heq, sub_self]
  exact sub_eq_zero.1 (eq_zero_on_support_of_wsum_sq_eq_zero hw h0 ω hω)

/-- **Reports equal on the support are endorsed given each other symmetrically**: `CondR i j`
and `V i = V j` on the support give `CondR j i`.
Source: mandate T6(d)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condR_symm_of_eq_on_support {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) {X : Finset Ω}
    {V : ι → Ω → ℝ} {i j : ι} (hij : CondR w X V i j) (heq : ∀ ω, 0 < w ω → V i ω = V j ω) :
    CondR w X V j i := by
  intro x y hxy
  obtain ⟨ω, hωE, hω⟩ := exists_pos_of_mass_pos hw hxy
  have hxyω : V i ω = x ∧ V j ω = y := by simpa using hωE
  have hxy' : x = y := by rw [← hxyω.1, ← hxyω.2, heq ω hω]
  subst hxy'
  rw [cls2_comm] at hxy ⊢
  exact hij x x hxy

/-- **Strict preference strictly increases resolution among calibrated reports**: `Prec i j` with
`V j` calibrated gives `E[V j²] < E[V i²]`.
Source: mandate T6(d)
Kind: P
Fidelity: n/a
Hyps: (a) all -/
theorem m2_lt_of_prec {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) {X : Finset Ω} {V : ι → Ω → ℝ} {i j : ι}
    (hij : Prec w X V i j) (hj : BeliefEndorses w X (V j)) : m2 w (V j) < m2 w (V i) := by
  rcases (m2_le_of_condR hw hij.1 hj).lt_or_eq with h | h
  · exact h
  · exact absurd (condR_symm_of_eq_on_support hw hij.1
      (eq_on_support_of_condR_of_m2_eq hw hij.1 hj h.symm)) hij.2

/-! ### (c) Acyclicity -/

/-- **T6(c): endorsed-given is acyclic — the three-cycle case** (P, the positive half of the
transitivity question): a three-cycle `CondR i j`, `CondR j k`, `CondR k i` collapses —
`V i = V j = V k` on the support. Each report is calibrated (it is the first index of some step),
so the three second-moment differences `E[V i²] − E[V j²]`, `E[V j²] − E[V k²]`,
`E[V k²] − E[V i²]` are non-negative and telescope to `0`; hence each is `0`, and equal second
moments force equality on the support. Two-cycles are covered by `k := i` (`CondR i i` follows
from `CondR i j` via `condR_self_iff`); cycles of every length are `condEndorse_cycle_collapse`
(the name here is kept for the ledger; it states the `n = 2` case), and `Prec`-cycles of every
length are excluded by `strictOrder_of_closure`.
Source: [[meaning-and-agency-reference]] §Conditional Endorsement, Q1 | udt-rep-2-015 | trust-lab-070 (T6(c))
Kind: P
Fidelity: variant: belief form on a finite frame; reports are random variables in `P₁`'s algebra; positive-mass guard; ATTRIBUTION-UNVETTED
Scope: finite `Ω`, positive-mass conditioning only (multiplicative form); FAF-free; says nothing about "optimization power"
Hyps: (a) all -/
theorem condEndorse_acyclic {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) {X : Finset Ω} {V : ι → Ω → ℝ}
    {i j k : ι} (hij : CondR w X V i j) (hjk : CondR w X V j k) (hki : CondR w X V k i) :
    ∀ ω, 0 < w ω → V i ω = V j ω ∧ V j ω = V k ω := by
  have ci : BeliefEndorses w X (V i) := beliefEndorses_of_condBeliefEndorses hw hij
  have cj : BeliefEndorses w X (V j) := beliefEndorses_of_condBeliefEndorses hw hjk
  have ck : BeliefEndorses w X (V k) := beliefEndorses_of_condBeliefEndorses hw hki
  have h1 := m2_le_of_condR hw hij cj
  have h2 := m2_le_of_condR hw hjk ck
  have h3 := m2_le_of_condR hw hki ci
  have eij : m2 w (V i) = m2 w (V j) := le_antisymm (by linarith) h1
  have ejk : m2 w (V j) = m2 w (V k) := le_antisymm (by linarith) h2
  intro ω hω
  exact ⟨eq_on_support_of_condR_of_m2_eq hw hij cj eij ω hω,
    eq_on_support_of_condR_of_m2_eq hw hjk ck ejk ω hω⟩

/-- **Conditional endorsement around a cycle of any length collapses** (the general form of
`condEndorse_acyclic`, which is the case `n = 2`; repair round 1, audit r1 fidelity N3): if the
reports `V (f 0), …, V (f n)` form a cycle of "endorsed given the next" (`CondR (f i) (f (i+1))`
for every `i : Fin (n+1)`, indices mod `n+1`), then every consecutive pair agrees on the support —
so all `n+1` reports are equal there. Every report on the cycle is calibrated (it is the first
index of a step), the second moment is non-increasing along each step, and since `i ↦ i + 1`
permutes the cycle the second moments have the same total before and after a step, so each step
is an equality; equal second moments under `CondR` force equality on the support. Two-cycles are
the case `n = 1`.
Source: [[meaning-and-agency-reference]] §Conditional Endorsement, Q1 | udt-rep-2-015 | trust-lab-070 (T6(c))
Kind: P
Fidelity: variant: belief form on a finite frame; positive-mass guard; says nothing about "optimization power"
Hyps: (a) all -/
theorem condEndorse_cycle_collapse {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) {X : Finset Ω} {V : ι → Ω → ℝ}
    {n : ℕ} {f : Fin (n + 1) → ι} (hcyc : ∀ i, CondR w X V (f i) (f (i + 1))) :
    ∀ i ω, 0 < w ω → V (f i) ω = V (f (i + 1)) ω := by
  have hcal : ∀ i, BeliefEndorses w X (V (f i)) := fun i =>
    beliefEndorses_of_condBeliefEndorses hw (hcyc i)
  have hstep : ∀ i, m2 w (V (f (i + 1))) ≤ m2 w (V (f i)) := fun i =>
    m2_le_of_condR hw (hcyc i) (hcal (i + 1))
  -- `i ↦ i + 1` permutes the cycle, so the second moments sum to the same total on both sides
  -- of the step inequality; a sum of `≤` with equal totals is pointwise `=`
  have hsum : ∑ i, m2 w (V (f (i + 1))) = ∑ i, m2 w (V (f i)) :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
  have heq : ∀ i, m2 w (V (f (i + 1))) = m2 w (V (f i)) := fun i =>
    (Finset.sum_eq_sum_iff_of_le (fun i _ => hstep i)).1 hsum i (Finset.mem_univ i)
  intro i ω hω
  exact eq_on_support_of_condR_of_m2_eq hw (hcyc i) (hcal (i + 1)) (heq i).symm ω hω

/-! ### (d) The transitive closure of `Prec` is a strict partial order -/

/-- Supporting lemma: along a `Prec`-chain from `i` to `j`, `V i` is calibrated, and if `V j` is
calibrated the second moment strictly drops from `i` to `j`.
Source: mandate T6(d)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem transGen_prec_calibrated_and_lt {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) {X : Finset Ω}
    {V : ι → Ω → ℝ} {i j : ι} (h : Relation.TransGen (Prec w X V) i j) :
    BeliefEndorses w X (V i) ∧ (BeliefEndorses w X (V j) → m2 w (V j) < m2 w (V i)) := by
  induction h with
  | single hij =>
    exact ⟨beliefEndorses_of_condBeliefEndorses hw hij.1, fun hj => m2_lt_of_prec hw hij hj⟩
  | tail _ hjk ih =>
    refine ⟨ih.1, fun hk => ?_⟩
    have hj : BeliefEndorses w X (V _) := beliefEndorses_of_condBeliefEndorses hw hjk.1
    exact (m2_lt_of_prec hw hjk hk).trans (ih.2 hj)

/-- **T6(d): the transitive closure of "strictly more trusted" is irreflexive** — no
`Prec`-cycle exists, with no calibration hypothesis: every index on a cycle is the first index
of a step and hence calibrated, and the second moment strictly decreases around the cycle.
Source: [[meaning-and-agency-reference]] §Conditional Endorsement, Q1 | udt-rep-2-015 (T6(d))
Kind: P
Fidelity: variant: belief form on a finite frame
Hyps: (a) all -/
theorem transGen_prec_irrefl {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (X : Finset Ω) (V : ι → Ω → ℝ)
    (i : ι) : ¬ Relation.TransGen (Prec w X V) i i := fun h =>
  lt_irrefl _ ((transGen_prec_calibrated_and_lt hw h).2 (transGen_prec_calibrated_and_lt hw h).1)

/-- **T6(d): `Prec⁺` is a strict partial order** (irreflexive and transitive): the surviving
neighbour of the refuted transitivity — the answer to the post's "can we use conditional
endorsement to (partially) order random variables" is "its transitive closure does".
Source: [[meaning-and-agency-reference]] §Conditional Endorsement, Q1 | udt-rep-2-015 (T6(d))
Kind: P
Fidelity: variant: belief form on a finite frame; the closure, not `Prec` itself (`prec_not_transitive`)
Hyps: (a) all -/
theorem strictOrder_of_closure {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (X : Finset Ω)
    (V : ι → Ω → ℝ) : IsStrictOrder ι (Relation.TransGen (Prec w X V)) where
  irrefl := transGen_prec_irrefl hw X V
  trans := fun _ _ _ hab hbc => hab.trans hbc

end

end Cleanroom.Udt.UdtEndorsePolicy
