import Cleanroom.Decision.DpFairnessReloc.AuditWitnesses

/-!
# Audit round 3 (adversarial) probe: EQ-4's `≈_val` and `≈_law` witnesses are payoff-constant;
a nested tree with non-constant payoffs passes both grades

Not imported by the library. Repair round 2 adopted `degen` (every payoff `0`) as the N+ for
"`≈_val` does not exclude nesting" (`degen_fairValEq`, ledger: "the best available for the
every-`C` grade") and `spur` (every leaf `(( ), 1)`) as the N+ for "`≈_law` only up to
law-spurious nesting" (`spur_lawFair`). On both trees the relation holds for a reason that has
nothing to do with nesting: `value C degen = 0` for every `C` (`probe_degen_value_constant`) and
`contLaw C spur = δ_{(( ),1)}` for every `C` (`probe_spur_law_constant`) — the "constant sequence"
pattern of [[STANDARDS]] §3, so both are N−.

The N+ that both rows can carry: `spurTop`, a `d`-node whose two children are one and the same
non-degenerate `d`-node `nb` (`a ↦ 1`, `b ↦ 0`). It is nested (`probe_spurTop_nested`), not
almost fair, its value is `q` under `procQ q` — so values and laws vary with the procedure
(`probe_spurTop_not_constant`) — and its one fiber `{top, bottom}` is law-fair
(`probe_spurTop_lawFair`), hence `Fair_{≈val}` (`probe_spurTop_fairValEq`) and `ValueFair`
(`probe_spurTop_valueFair`); it is not strongly fair (`probe_spurTop_not_stronglyFair`, node
count). The mechanism is the one the source's phrase "law-spurious nesting" names: the nested
query is invisible to the law because its children are law-equal, not because the payoffs are
flat. So "a non-degenerate nested tree is rejected by `≈_val` whenever the nested point changes
the value" (ledger) is right, and "the best available" is not.
-/

namespace Cleanroom.Decision.DpFairnessReloc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

/-! ### The adopted witnesses are constant in the procedure -/

theorem probe_degen_value_constant (C C' : Proc Unit (fun _ => Act2) ℚ) :
    value C degen = value C' degen := by
  rw [degen_value, degen_value]

theorem probe_spur_law_constant (C C' : Proc Unit (fun _ => Act2) ℚ) :
    contLaw C spur = contLaw C' spur := by
  rw [contLaw_spur, contLaw_spur]

/-! ### A non-degenerate nested tree that is law-fair and `≈_val`-fair -/

/-- A `d`-node with payoffs `1` under `a` and `0` under `b`. -/
def nb : Tree Unit Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .leaf () 1
    | .b => .leaf () 0

/-- A spurious `d`-query over `nb`: both children are `nb`. -/
def spurTop : Tree Unit Unit (fun _ => Act2) ℚ := .decision () fun _ => nb

theorem probe_contLaw_spurTop (C : Proc Unit (fun _ => Act2) ℚ) :
    contLaw C spurTop = contLaw C nb := by
  unfold spurTop
  rw [contLaw_decision, ← Finset.sum_smul, (C ()).sum_one, one_smul]

theorem probe_spurTop_subtree (q : spurTop.DecNode) :
    subtreeAt spurTop q = spurTop ∨ subtreeAt spurTop q = nb := by
  rcases q with _ | ⟨a, _ | ⟨b, e⟩⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · cases b <;> (change Empty at e; exact e.elim)

theorem probe_spurTop_nested : Nested spurTop () := by
  refine ⟨by decide, ⟨.a, ⟨.a, ()⟩⟩, ?_, ?_⟩
  · unfold Positive spurTop nb; simp
  · decide

theorem probe_spurTop_not_almostFair : ¬ AlmostFair spurTop := fun h =>
  absurd (h () ⟨.a, ⟨.a, ()⟩⟩) (by decide)

theorem probe_spurTop_lawFair : LawFair spurTop := by
  intro d q _ q' _ C
  rcases probe_spurTop_subtree q with h | h <;> rcases probe_spurTop_subtree q' with h' | h' <;>
    rw [h, h'] <;> simp only [probe_contLaw_spurTop]

theorem probe_spurTop_fairValEq : FairWrt (fun _ => ValEq) spurTop := by
  intro d q hq q' hq' C
  exact value_eq_of_contLaw_eq C (probe_spurTop_lawFair d q hq q' hq' C)

theorem probe_spurTop_valueFair : ValueFair spurTop := by
  intro d q hq q' hq' C a
  exact value_eq_of_contLaw_eq _ (probe_spurTop_lawFair d q hq q' hq' _)

theorem probe_nb_value (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) nb = q := by
  unfold value nb
  rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
  simp [procQ]

theorem probe_spurTop_value (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) spurTop = q := by
  rw [value_eq_of_contLaw_eq _ (probe_contLaw_spurTop _), probe_nb_value]

/-- Non-degeneracy: the value of the nested tree, and of each fiber member, varies with `C`. -/
theorem probe_spurTop_not_constant :
    value (procQ 1 (by norm_num) (by norm_num)) spurTop ≠
      value (procQ 0 (by norm_num) (by norm_num)) spurTop := by
  rw [probe_spurTop_value, probe_spurTop_value]; norm_num

theorem probe_spurTop_not_stronglyFair : ¬ StronglyFair spurTop := by
  intro h
  have := h () none (by decide) (some ⟨.a, none⟩) (by decide)
  change LabIso spurTop nb at this
  exact absurd (LabIso.size_eq this) (by decide)

/-- The bundle: nested, not almost fair, not strongly fair, non-constant in `C`, and fair in the
`≈_law`, `≈_val` and act-value grades. -/
theorem probe_nondegen_nested_val_law :
    Nested spurTop () ∧ ¬ AlmostFair spurTop ∧ ¬ StronglyFair spurTop ∧
      value (procQ 1 (by norm_num) (by norm_num)) spurTop ≠
        value (procQ 0 (by norm_num) (by norm_num)) spurTop ∧
      LawFair spurTop ∧ FairWrt (fun _ => ValEq) spurTop ∧ ValueFair spurTop :=
  ⟨probe_spurTop_nested, probe_spurTop_not_almostFair, probe_spurTop_not_stronglyFair,
    probe_spurTop_not_constant, probe_spurTop_lawFair, probe_spurTop_fairValEq,
    probe_spurTop_valueFair⟩

end Cleanroom.Decision.DpFairnessReloc
