/-
  negative-voi.lean  —  Round-2 lab, TODO `negative-voi`  (modality: LEAN-CORE)

  CLAIM (acceptance target).  Build Weatherson's 3-world *tightness* example (cited but not
  built in deference-in-logical-induction-v2.md §1.1, line 241): two experts E1, E2, BOTH
  reflexive+transitive+nested (S4), with E2 NON-partitional, and a menu O of [0,1]-options,
  such that — with the recommended strategy of each expert defined as the GENUINE
  argmax-of-its-own-posterior (smallest-index tie-break, applied identically to both) —
       (i)  Value(E1) < Value(E2)   STRICTLY      (value of information is NEGATIVE), and
       (ii) NEAR-MISS: replacing E2 by a PARTITIONAL anchor Q (E1 still refines it) restores
            Value(E1) ≥ Value(Q)    (Blackwell–Geanakoplos monotonicity).
  (ii) certifies the negative sign in (i) is caused by E2's NON-partitionality, not by the
  payoffs: the SAME π, the SAME menu O, the SAME definition of recommended strategy.

  ── Anti-fake notes (this file is LEAN-CORE; the hard objects are NOT hypotheses) ──
  * No logical-induction theorem, no martingale, no asymptotic `≂ₙ` object appears anywhere —
    not as a hypothesis, not as an encoding.  Everything is a finite ℚ computation over Fin 3.
  * The recommended strategy is `recOpt E w := argmaxⱼ (Σ_{u∈E(w)} π u · O j u)` — the genuine
    argmax of expert E's own posterior, COMPUTED from π and E.  It is NOT hand-fed and NOT
    defined adversarially; the IDENTICAL rule (and IDENTICAL smallest-index tie-break) is used
    for E1, E2, and Q.  (Defeats shadow-test (a).)  In THIS witness the choice is in fact a
    STRICT argmax at world 2 for every expert (no tie is used — see the `*_world2_strict`
    lemmas and `recOpt_*` lemmas), so the gap does not even rely on the tie-break.
  * Argmax of the conditional-expectation NUMERATOR = argmax of the posterior, because the two
    options share the SAME conditioning cell at a fixed world (same denominator `π(E(w))`).
    Lemma `recOpt_eq_posterior_argmax` certifies this: `recOpt` agrees with the argmax of the
    NORMALIZED posterior.  So dropping the denominator is a faithful shortcut, not a different
    selection rule.
  * `Value(E1) < Value(E2)` is the CONCLUSION (`norm_num`), never a hypothesis.
    (Defeats shadow-test (b).)
  * The mandatory partitional near-miss (ii) compiles and flips the inequality back to `≥` —
    STRICTLY, `Value Q < Value E2` while `Value Q ≤ Value E1` — so (i) is not a payoff artifact.
    (Defeats shadow-test (c).)
  * This does NOT re-skin `value_of_CM` / `value_of_argmax` / `payoff_gap_le_l1` (the single-
    expert positive-Value route) nor the `AntiExpert` frame (one expert vs an unconditional
    martingale): this is a TWO-expert comparison and the driver is non-partitionality.

  Concrete witness (worlds W = Fin 3, π uniform = (1/3,1/3,1/3)):
    Menu (two [0,1]-options):  O⁰ = (0, 2/3, 1/3),  O¹ = (2/3, 0, 0).
    E1 (finer, S4, non-partitional):  E1(0)={0},  E1(1)={1},  E1(2)={0,2}
    E2 (coarser, S4, NON-partitional): E2(0)={0}, E2(1)={1},  E2(2)={0,1,2}
    Q  (partition anchor, partitional): Q(0)={0,2}, Q(1)={1}, Q(2)={0,2}
  E1 refines E2 and refines Q (E1(w) ⊆ E2(w), E1(w) ⊆ Q(w) for all w).
  Mechanism (strict, no tie at world 2): E1 sees {0,2} and STRICTLY prefers O¹ (posterior
  numerators 2/9 > 1/9), which pays 0 at world 2; E2 sees {0,1,2} and STRICTLY prefers O⁰
  (1/3 > 2/9 — world 1's high O⁰ payoff pulls E2's posterior up), which pays 1/3 — the COARSER
  expert's recommended diagonal return is higher.
  Values: Value(E1)=4/9,  Value(E2)=5/9,  Value(Q)=4/9.  (4/9 < 5/9;  4/9 ≥ 4/9.)

  Independently cross-checked by exhaustive ℚ search in run2/work/negative-voi.py.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open Finset

namespace NegativeVoI

/-- Worlds. -/
abbrev W := Fin 3

/-- An "experiment"/expert is, at each world, its information set E(w) ⊆ W, given as a
    decidable membership predicate.  (Everything below is finite & decidable.) -/
abbrev Info := W → W → Bool      -- `E w u = true`  ↔  `u ∈ E(w)`

/-- The prior π (uniform on the three worlds). -/
def π : W → ℚ := fun _ => 1/3

/-- The menu: two bounded [0,1]-options.  `O j w` is option j's payoff at world w. -/
def O : Fin 2 → W → ℚ
  | 0, 0 => 0   | 0, 1 => 2/3 | 0, 2 => 1/3
  | 1, 0 => 2/3 | 1, 1 => 0   | 1, 2 => 0

/-- The three experiments. -/
def E1 : Info
  | 0, u => decide (u = 0)
  | 1, u => decide (u = 1)
  | 2, u => decide (u = 0 ∨ u = 2)

def E2 : Info
  | 0, u => decide (u = 0)
  | 1, u => decide (u = 1)
  | 2, _ => true                       -- world 2 sees everything

/-- Partition anchor: the cells are {0,2} and {1} — a genuine partition. -/
def Q : Info
  | 0, u => decide (u = 0 ∨ u = 2)
  | 1, u => decide (u = 1)
  | 2, u => decide (u = 0 ∨ u = 2)

/-! ### S4 structure of the experiments — proved (NOT assumed).

These predicates are `abbrev`s so the kernel unfolds them for `decide`; each is a decidable
`∀`/`∨`/`¬∧` over `Fin 3` with `Bool`-valued atoms. -/

/-- reflexive: `w ∈ E(w)`. -/
abbrev Reflexive (E : Info) : Prop := ∀ w, E w w = true
/-- transitive (positive introspection): `v ∈ E(w) → E(v) ⊆ E(w)`. -/
abbrev Transitive (E : Info) : Prop := ∀ w v u, E w v = true → E v u = true → E w u = true
/-- nested: for all `w,v` the sets `E(w), E(v)` are disjoint or one contains the other. -/
abbrev Nested (E : Info) : Prop :=
  ∀ w v, (∀ u, ¬ (E w u = true ∧ E v u = true))
         ∨ (∀ u, E w u = true → E v u = true)
         ∨ (∀ u, E v u = true → E w u = true)
/-- S4 = reflexive ∧ transitive ∧ nested. -/
abbrev S4 (E : Info) : Prop := Reflexive E ∧ Transitive E ∧ Nested E
/-- Euclidean (negative introspection): `v ∈ E(w) → E(w) ⊆ E(v)`.  S4+Euclidean = S5 = partitional. -/
abbrev Euclidean (E : Info) : Prop := ∀ w v u, E w v = true → E w u = true → E v u = true
/-- partitional := S4 ∧ Euclidean. -/
abbrev Partitional (E : Info) : Prop := S4 E ∧ Euclidean E

-- All three experiments are S4.
theorem E1_S4 : S4 E1 := by decide
theorem E2_S4 : S4 E2 := by decide
theorem Q_S4  : S4 Q  := by decide

-- E2 is NON-partitional: its Euclidean property FAILS (witness w=2,v=0: 0∈E2(2)=all but 2∉E2(0)={0}).
theorem E2_not_partitional : ¬ Partitional E2 := by decide
-- The partition anchor Q *is* partitional (this is what makes the near-miss legitimate).
theorem Q_partitional : Partitional Q := by decide
-- For contrast, E1 is also non-partitional (so the comparison is S4-vs-S4, not S5-vs-S4).
theorem E1_not_partitional : ¬ Partitional E1 := by decide

/-! ### Refinement: E1 is more refined than E2 and than Q. -/

/-- `Refines Ea Eb` : Ea is (weakly) more informative — every Ea info-set sits inside the Eb one. -/
abbrev Refines (Ea Eb : Info) : Prop := ∀ w u, Ea w u = true → Eb w u = true

theorem E1_refines_E2 : Refines E1 E2 := by decide
theorem E1_refines_Q  : Refines E1 Q  := by decide

/-! ### Recommended strategy = genuine argmax of the expert's OWN posterior.

`condNum E j w := Σ_{u ∈ E(w)} π u · O j u` is the numerator of the conditional expectation
`E_π(Oʲ | E(w))` (the denominator `π(E(w))` is the same for both options at a fixed `w`, so
argmax over j of the numerator = argmax of the posterior).  `recOpt E w` is the argmax with the
explicit smallest-index tie-break (option 0 wins ties).  The SAME rule is used for E1, E2, Q. -/

def condNum (E : Info) (j : Fin 2) (w : W) : ℚ :=
  ∑ u : W, (if E w u then π u * O j u else 0)

/-- Cell mass `π(E(w)) = Σ_{u∈E(w)} π u`, the common denominator of the posterior. -/
def condMass (E : Info) (w : W) : ℚ :=
  ∑ u : W, (if E w u then π u else 0)

/-- Posterior expectation `E_π(Oʲ | E(w))` (normalized). -/
def posterior (E : Info) (j : Fin 2) (w : W) : ℚ := condNum E j w / condMass E w

/-- Recommended option at world `w` for expert `E` (two options; ties → option 0). -/
def recOpt (E : Info) (w : W) : Fin 2 :=
  if condNum E 1 w > condNum E 0 w then 1 else 0

/-- Diagonal return of the recommended strategy at world `w`: the chosen option, paid AT `w`. -/
def recPayoff (E : Info) (w : W) : ℚ := O (recOpt E w) w

/-- **Value(E)** = π-average of the diagonal recommended return = `Σ_w π(w) · O^{rec}(w)`. -/
def Value (E : Info) : ℚ := ∑ w : W, π w * recPayoff E w

/-! ### Faithfulness: `recOpt` is genuinely the argmax of the NORMALIZED posterior.

Cell masses are positive, so `condNum 1 > condNum 0 ↔ posterior 1 > posterior 0`.  This shows
dropping the common denominator did not change the selection — `recOpt` is the posterior argmax,
not a different rule. -/

theorem condMass_pos (E : Info) (w : W) (hw : E w w = true) : 0 < condMass E w := by
  unfold condMass
  refine Finset.sum_pos' (fun u _ => ?_) ⟨w, Finset.mem_univ w, ?_⟩
  · by_cases h : E w u = true
    · rw [if_pos h]; norm_num [π]
    · simp only [Bool.not_eq_true] at h; rw [if_neg (by rw [h]; simp)]
  · rw [if_pos hw]; norm_num [π]

/-- **`recOpt` = posterior argmax.**  Because `condMass E w > 0` (the cell is nonempty, `w ∈ E w`),
    `condNum E 1 w > condNum E 0 w ↔ posterior E 1 w > posterior E 0 w`, so `recOpt` (defined on
    the numerators) is exactly the argmax of the normalized posterior `E_π(Oʲ | E w)`. -/
theorem recOpt_eq_posterior_argmax (E : Info) (w : W) (hw : E w w = true) :
    recOpt E w = (if posterior E 1 w > posterior E 0 w then 1 else 0) := by
  have hm : 0 < condMass E w := condMass_pos E w hw
  have hiff : (condNum E 1 w > condNum E 0 w) ↔ (posterior E 1 w > posterior E 0 w) := by
    unfold posterior
    rw [gt_iff_lt, gt_iff_lt, div_lt_div_iff_of_pos_right hm]
  unfold recOpt
  exact if_congr hiff rfl rfl

/-! ### Per-world recommended choices (computed; the world-2 ones are STRICT argmaxes). -/

/-- Reduce a concrete `condNum E j w` to an explicit rational: expand the 3-world sum, then
    decide the membership guards and evaluate the menu matches. -/
theorem condNum_eval (E : Info) (j : Fin 2) (w : W) :
    condNum E j w
      = (if E w 0 then π 0 * O j 0 else 0)
      + (if E w 1 then π 1 * O j 1 else 0)
      + (if E w 2 then π 2 * O j 2 else 0) := by
  simp only [condNum, Fin.sum_univ_three]

-- world-0 and world-1 cells are singletons; world-2 is the interesting strict case.
theorem recOpt_E1_0 : recOpt E1 0 = 1 := by
  rw [recOpt, condNum_eval, condNum_eval]; simp [E1, O, π] <;> norm_num
theorem recOpt_E1_1 : recOpt E1 1 = 0 := by
  rw [recOpt, condNum_eval, condNum_eval]; simp [E1, O, π] <;> norm_num
/-- world 2: E1 sees {0,2}, STRICTLY prefers O¹ (numerators 2/9 > 1/9). -/
theorem recOpt_E1_2 : recOpt E1 2 = 1 := by
  rw [recOpt, condNum_eval, condNum_eval]; simp [E1, O, π] <;> norm_num
theorem E1_world2_strict : condNum E1 0 2 < condNum E1 1 2 := by
  rw [condNum_eval, condNum_eval]; simp [E1, O, π] <;> norm_num

theorem recOpt_E2_0 : recOpt E2 0 = 1 := by
  rw [recOpt, condNum_eval, condNum_eval]; simp [E2, O, π] <;> norm_num
theorem recOpt_E2_1 : recOpt E2 1 = 0 := by
  rw [recOpt, condNum_eval, condNum_eval]; simp [E2, O, π] <;> norm_num
/-- world 2: E2 sees {0,1,2}, STRICTLY prefers O⁰ (numerators 1/3 > 2/9). -/
theorem recOpt_E2_2 : recOpt E2 2 = 0 := by
  rw [recOpt, condNum_eval, condNum_eval]; simp [E2, O, π] <;> norm_num
theorem E2_world2_strict : condNum E2 1 2 < condNum E2 0 2 := by
  rw [condNum_eval, condNum_eval]; simp [E2, O, π] <;> norm_num

theorem recOpt_Q_0 : recOpt Q 0 = 1 := by
  rw [recOpt, condNum_eval, condNum_eval]; simp [Q, O, π] <;> norm_num
theorem recOpt_Q_1 : recOpt Q 1 = 0 := by
  rw [recOpt, condNum_eval, condNum_eval]; simp [Q, O, π] <;> norm_num
theorem recOpt_Q_2 : recOpt Q 2 = 1 := by
  rw [recOpt, condNum_eval, condNum_eval]; simp [Q, O, π] <;> norm_num

/-! ### The witness values, computed from the per-world recommended choices. -/

theorem Value_E1 : Value E1 = 4/9 := by
  simp only [Value, recPayoff, Fin.sum_univ_three, recOpt_E1_0, recOpt_E1_1, recOpt_E1_2, O, π]
  norm_num
theorem Value_E2 : Value E2 = 5/9 := by
  simp only [Value, recPayoff, Fin.sum_univ_three, recOpt_E2_0, recOpt_E2_1, recOpt_E2_2, O, π]
  norm_num
theorem Value_Q : Value Q = 4/9 := by
  simp only [Value, recPayoff, Fin.sum_univ_three, recOpt_Q_0, recOpt_Q_1, recOpt_Q_2, O, π]
  norm_num

/-! ### Headline results. -/

/-- **(i) NEGATIVE value of information (the strict gap is the CONCLUSION).**
    The more-refined S4 expert E1 has STRICTLY LOWER recommended-strategy Value than the
    coarser, NON-partitional S4 expert E2.  No LI/asymptotic object appears. -/
theorem negative_VoI : Value E1 < Value E2 := by
  rw [Value_E1, Value_E2]; norm_num

/-- **(ii) MANDATORY NEAR-MISS — partitional anchor restores Geanakoplos monotonicity.**
    With E2 replaced by the PARTITIONAL anchor Q (E1 still refines it, same π, same menu),
    the inequality flips back: the more-refined E1 is at least as good.  This certifies the
    negative sign in (i) is caused by E2's NON-partitionality, not by the payoffs. -/
theorem near_miss_partitional : Value Q ≤ Value E1 := by
  rw [Value_E1, Value_Q]

/-- Non-vacuity of the near-miss, the OTHER direction: the SAME menu makes the NON-partitional
    E2 STRICTLY beat the partitional anchor Q, so the sign genuinely tracks partitionality:
    `Value Q ≤ Value E1 < Value E2`. -/
theorem partitional_anchor_strictly_dominated : Value Q < Value E2 := by
  rw [Value_Q, Value_E2]; norm_num

/-- Package: the strict negative gap together with its certificate that
    (a) both experts are S4, (b) E2 is non-partitional while the near-miss anchor Q is
    partitional, (c) E1 refines both, and (d) the near-miss flips the sign. -/
theorem tightness_witness :
    S4 E1 ∧ S4 E2 ∧ S4 Q ∧
    ¬ Partitional E2 ∧ Partitional Q ∧
    Refines E1 E2 ∧ Refines E1 Q ∧
    Value E1 < Value E2 ∧            -- (i) negative VoI, strict
    Value Q ≤ Value E1 := by         -- (ii) partitional near-miss restores monotonicity
  exact ⟨E1_S4, E2_S4, Q_S4, E2_not_partitional, Q_partitional,
         E1_refines_E2, E1_refines_Q, negative_VoI, near_miss_partitional⟩

end NegativeVoI

#print axioms NegativeVoI.E1_S4
#print axioms NegativeVoI.E2_S4
#print axioms NegativeVoI.Q_S4
#print axioms NegativeVoI.E2_not_partitional
#print axioms NegativeVoI.Q_partitional
#print axioms NegativeVoI.E1_not_partitional
#print axioms NegativeVoI.E1_refines_E2
#print axioms NegativeVoI.E1_refines_Q
#print axioms NegativeVoI.condMass_pos
#print axioms NegativeVoI.recOpt_eq_posterior_argmax
#print axioms NegativeVoI.E1_world2_strict
#print axioms NegativeVoI.E2_world2_strict
#print axioms NegativeVoI.Value_E1
#print axioms NegativeVoI.Value_E2
#print axioms NegativeVoI.Value_Q
#print axioms NegativeVoI.negative_VoI
#print axioms NegativeVoI.near_miss_partitional
#print axioms NegativeVoI.partitional_anchor_strictly_dominated
#print axioms NegativeVoI.tightness_witness
