import Cleanroom.Decision.DpLearnerNr.Defs

/-!
# `dp-learner-nr` target 1(a)(b): the leak and the unshielded-marginal threshold

**The leak** ([[non-responsiveness]] "NR2"): for a finitely additive `P` on a finite world type
and events `Cross`, `Incon`, if `P(Cross → Incon) ≥ 1 − ε` then
`P(Incon) ≥ P(Cross ∧ Incon) ≥ P(Cross) − ε` (`leak_inter`, `leak`). Hence an NR1 rule whose
marginal is `P`'s own `Incon`-marginal — crossing iff `P(Incon) < ½` — crosses only if
`P(Cross) < ½ + ε` (`nr1_unshielded_threshold`): the marginal formula does not shield the
marginal, which is why NR1 alone does not give NR2.

Witnesses: on `Bool × Bool` (cross, incon), `P(Cross) = 9/10`, `ε = 1/100`, `P(Incon) = 89/100`
(the rule stays), and the crossing instance `P(Cross) = 2/5`, `P(Incon) = 39/100 < ½`.
The grid number `19/40` of [[non-responsiveness-learnability]] §8 B is a grid artifact
(findings).
-/

namespace Cleanroom.Decision.DpLearnerNr

open Cleanroom.Found.DpCoreTree Cleanroom.Decision.DpCalibration Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- `Cross \ Incon` and `Crossᶜ ∪ Incon` partition the worlds. Source: none: infrastructure. Kind: L -/
theorem probOf_sdiff_add_compl_union (P : FinDistr K Ω) (Cross Incon : Finset Ω) :
    probOf P (Cross \ Incon) + probOf P (Crossᶜ ∪ Incon) = 1 := by
  have hdisj : Disjoint (Cross \ Incon) (Crossᶜ ∪ Incon) := by
    rw [Finset.disjoint_left]
    intro ω h1 h2
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_compl] at h1 h2
    tauto
  have huniv : (Cross \ Incon) ∪ (Crossᶜ ∪ Incon) = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro ω
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_compl]
    tauto
  rw [← probOf_union P hdisj, huniv, probOf_univ]

/-- `P(Cross) = P(Cross ∧ Incon) + P(Cross \ Incon)`. Source: none: infrastructure. Kind: L -/
theorem probOf_inter_add_sdiff (P : FinDistr K Ω) (Cross Incon : Finset Ω) :
    probOf P (Cross ∩ Incon) + probOf P (Cross \ Incon) = probOf P Cross := by
  unfold probOf
  exact Finset.sum_inter_add_sum_sdiff Cross Incon _

/-- **The leak, first inequality**: if `P(Cross → Incon) ≥ 1 − ε` then
`P(Cross ∧ Incon) ≥ P(Cross) − ε`. Finite additivity: `P(Cross \ Incon) = 1 − P(Crossᶜ ∪ Incon) ≤ ε`.
Source: [[non-responsiveness]] "NR2 (marginal shielding)" ("a believed theorem `Cross → □⊥`
forces `P(□⊥) ≥ P(Cross ∧ (Cross → □⊥)) ≥ P(Cross) − ε`"); [[dp-core-inventory]] 104;
[[dp-learner-nr-mandate]] target 1(a)
Kind: P
Fidelity: exact (the `ε` form; the `= 1` form is the instance `ε = 0`)
Hyps: (a) none -/
theorem leak_inter (P : FinDistr K Ω) (Cross Incon : Finset Ω) (ε : K)
    (h : 1 - ε ≤ probOf P (Crossᶜ ∪ Incon)) :
    probOf P Cross - ε ≤ probOf P (Cross ∩ Incon) := by
  have h1 := probOf_inter_add_sdiff P Cross Incon
  have h2 := probOf_sdiff_add_compl_union P Cross Incon
  linarith

/-- **The leak, second inequality**: `P(Incon) ≥ P(Cross ∧ Incon)` (monotonicity).
Source: [[non-responsiveness]] "NR2"; [[dp-learner-nr-mandate]] target 1(a)
Kind: L -/
theorem leak_mono (P : FinDistr K Ω) (Cross Incon : Finset Ω) :
    probOf P (Cross ∩ Incon) ≤ probOf P Incon :=
  probOf_mono P Finset.inter_subset_right

/-- **The leak** (load-bearing 1): a coherent credence over a language containing `Cross` that
believes `Cross → Incon` to degree `≥ 1 − ε` has `P(Incon) ≥ P(Cross) − ε` — the marginal is
moved through the self-prediction, so NR1 does not give NR2.
Source: [[non-responsiveness]] "NR2 (marginal shielding)" and "**The leak** [derived; checked]";
[[non-responsiveness-learnability]] §1 NR2; [[dp-core-inventory]] 104;
[[dp-learner-nr-mandate]] target 1(a), load-bearing 1
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem leak (P : FinDistr K Ω) (Cross Incon : Finset Ω) (ε : K)
    (h : 1 - ε ≤ probOf P (Crossᶜ ∪ Incon)) :
    probOf P Cross - ε ≤ probOf P Incon :=
  (leak_inter P Cross Incon ε h).trans (leak_mono P Cross Incon)

/-- The `= 1` instance of the leak: a believed theorem (`P(Cross → Incon) = 1`) gives
`P(Incon) ≥ P(Cross)`.
Source: [[non-responsiveness]] "NR2"; [[dp-learner-nr-mandate]] target 1 trap (i)
Kind: L -/
theorem leak_of_eq_one (P : FinDistr K Ω) (Cross Incon : Finset Ω)
    (h : probOf P (Crossᶜ ∪ Incon) = 1) : probOf P Cross ≤ probOf P Incon := by
  have := leak P Cross Incon 0 (by rw [h]; simp)
  linarith

/-! ## The NR1 rule with an unshielded marginal -/

/-- The `Incon`-marginal of `P` on `Bool`: the pushforward along membership in `Incon`.
Source: [[non-responsiveness]] "NR2" ("if the marginal is the agent's ordinary coherent
credence `P` over a language containing `Cross`")
Kind: D -/
def inconMarginal (P : FinDistr K Ω) (Incon : Finset Ω) : FinDistr K Bool :=
  pushDistr P fun ω => decide (ω ∈ Incon)

/-- The marginal's weight on `true` is `P(Incon)`. Source: none: infrastructure. Kind: L -/
theorem inconMarginal_w_true (P : FinDistr K Ω) (Incon : Finset Ω) :
    (inconMarginal P Incon).w true = probOf P Incon := by
  rw [inconMarginal, pushDistr_w]
  congr 1
  ext ω; simp

/-- **The NR1 rule on an unshielded marginal crosses iff `P(Incon) < ½`**: the marginal
formula with the troll's table, fed `P`'s own `Incon`-marginal.
Source: [[non-responsiveness]] "NR1"; [[dp-learner-nr-mandate]] target 1(b)
Kind: L -/
theorem nr1_unshielded_cross_iff (P : FinDistr K Ω) (Incon : Finset Ω) :
    cfMarginal (inconMarginal P Incon) trollE Act2.b
        < cfMarginal (inconMarginal P Incon) trollE Act2.a
      ↔ probOf P Incon < 1 / 2 := by
  rw [cfMarginal_trollE_cross_pos_iff, inconMarginal_w_true]

/-- **The unshielded threshold** (load-bearing 1(b)): an NR1 rule whose marginal is the agent's
own coherent credence, believing `Cross → Incon` to degree `≥ 1 − ε`, crosses only if
`P(Cross) < ½ + ε`. (The note's gloss — "under the hypothetical proof every crossing is a
self-mispredicted one" — is the reading of this inequality, not part of the theorem.)
Source: [[non-responsiveness]] "NR2" ("the largest coherent `P(cross)` at which it still
crosses is below `½ + ε` [checked]"); [[non-responsiveness-learnability]] §8 B;
[[dp-core-2-inventory]] 039; [[dp-learner-nr-mandate]] target 1(b)
Kind: P
Fidelity: exact (the theorem is `P(Cross) < ½ + ε`; the note's `19/40` is its grid instance at
`ε = 1/100`, step `1/40` — findings)
Hyps: (a) none -/
theorem nr1_unshielded_threshold (P : FinDistr K Ω) (Cross Incon : Finset Ω) (ε : K)
    (hleak : 1 - ε ≤ probOf P (Crossᶜ ∪ Incon))
    (hcross : cfMarginal (inconMarginal P Incon) trollE Act2.b
      < cfMarginal (inconMarginal P Incon) trollE Act2.a) :
    probOf P Cross < 1 / 2 + ε := by
  rw [nr1_unshielded_cross_iff] at hcross
  have := leak P Cross Incon ε hleak
  linarith

/-! ## Witnesses on `Bool × Bool` (cross, incon) -/

/-- A distribution on `(cross, incon)` pairs with the four weights given.
Source: none: infrastructure
Kind: D -/
def twoBit (a b c d : K) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hsum : a + b + c + d = 1) : FinDistr K (Bool × Bool) where
  w := fun
    | (true, true) => a
    | (true, false) => b
    | (false, true) => c
    | (false, false) => d
  nonneg := by rintro ⟨x, y⟩; cases x <;> cases y <;> assumption
  sum_one := by
    rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    linarith

/-- The crossing event `{cross = true}`. Source: none: infrastructure. Kind: D -/
def crossEv : Finset (Bool × Bool) := univ.filter fun w => w.1 = true

/-- The inconsistency event `{incon = true}`. Source: none: infrastructure. Kind: D -/
def inconEv : Finset (Bool × Bool) := univ.filter fun w => w.2 = true

/-- The witness distribution: `P(Cross) = 9/10`, `P(Incon) = 89/100`, `P(Cross \ Incon) = 1/100`.
Source: [[dp-learner-nr-mandate]] target 1 trap (iv)
Kind: D -/
def leakWitness : FinDistr ℚ (Bool × Bool) :=
  twoBit (89/100) (1/100) 0 (1/10) (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num)

/-- **N+ for the leak**: `P(Cross) = 9/10`, `ε = 1/100`, the hypothesis `P(Cross → Incon) = 99/100`
holds, and `P(Incon) = 89/100 ≥ P(Cross) − ε`; the NR1 rule *stays* (`89/100 ≥ ½`).
Source: [[dp-learner-nr-mandate]] target 1 trap (iv)
Kind: N+ -/
theorem leakWitness_facts :
    probOf leakWitness crossEv = 9/10 ∧
    probOf leakWitness inconEv = 89/100 ∧
    probOf leakWitness (crossEvᶜ ∪ inconEv) = 1 - 1/100 ∧
    ¬ (cfMarginal (inconMarginal leakWitness inconEv) trollE Act2.b
        < cfMarginal (inconMarginal leakWitness inconEv) trollE Act2.a) := by
  rw [nr1_unshielded_cross_iff]
  simp only [probOf_eq_sum_ite, Fintype.sum_prod_type, Fintype.sum_bool, crossEv, inconEv,
    Finset.mem_union, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
  simp [leakWitness, twoBit]
  norm_num

/-- The crossing instance: `P(Cross) = 2/5`, `P(Incon) = 39/100`, `P(Cross \ Incon) = 1/100`.
Source: [[dp-learner-nr-mandate]] target 1 trap (iv)
Kind: D -/
def crossWitness : FinDistr ℚ (Bool × Bool) :=
  twoBit (39/100) (1/100) 0 (3/5) (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num)

/-- **N+ for the threshold**: `P(Cross) = 2/5`, `P(Incon) = 39/100 < ½` (the rule crosses), the
leak hypothesis holds at `ε = 1/100`, and `P(Cross) = 2/5 < ½ + 1/100`.
Source: [[dp-learner-nr-mandate]] target 1 trap (iv)
Kind: N+ -/
theorem crossWitness_facts :
    probOf crossWitness crossEv = 2/5 ∧
    probOf crossWitness inconEv = 2/5 - 1/100 ∧
    probOf crossWitness (crossEvᶜ ∪ inconEv) = 1 - 1/100 ∧
    (cfMarginal (inconMarginal crossWitness inconEv) trollE Act2.b
        < cfMarginal (inconMarginal crossWitness inconEv) trollE Act2.a) ∧
    probOf crossWitness crossEv < 1/2 + 1/100 := by
  rw [nr1_unshielded_cross_iff]
  simp only [probOf_eq_sum_ite, Fintype.sum_prod_type, Fintype.sum_bool, crossEv, inconEv,
    Finset.mem_union, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
  simp [crossWitness, twoBit]
  norm_num

end Cleanroom.Decision.DpLearnerNr
