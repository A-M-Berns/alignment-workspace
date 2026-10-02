import Cleanroom.Bli.BliRvcUi.Ui.Limit
import Cleanroom.Bli.BliRvcUi.Ui.Lia
import Cleanroom.Bli.BliFound.PaperInstances
import Cleanroom.Bli.BliFound.Extend

/-!
# `bli-rvc-ui` · Ui/Free: universal instantiation on undecided instances (repair round 1)

**Why this file exists.** Audit round 1 (both lenses) found that the package's two
universal-instantiation witnesses used the instance family `trueInst T` — theorems of the base —
so the schema `u 🡒 inst c` was inert in the limit: `UILimit` reduced to `P∞(u) ≤ 1`
(`uiLimit_of_inst_limit_one`), and the sibling prime of T3.7 (b) did no work (`⊤` entails a
theorem). The families here have **free instance atoms**: pairwise distinct fresh atoms (family
`9`, payloads `⟨2, c⟩`) that no base process mentions, tied to the universal-role atom
`u := freshAtom 9 ⟨1, 0⟩` (and its sibling `u' := freshAtom 9 ⟨1, 1⟩`) only through the schema
process. Over any base whose stages mention no family-`9` atom:

* **`ui_free_nontrivial` — the N+ for T3.3 `ui_limit_of_union`**: `0 < P∞(u) < P∞(inst c) < 1`
  for every inductor over `DP ∪ Ax(freeUI)`. Both sides are interior and the middle inequality is
  strict: the schema forces `P∞(u ⋏ ∼inst c) = 0`, non-dogmatism gives `P∞(inst c ⋏ ∼u) > 0`
  (`limitingBelief_lt_of_theory_imp`). No `[0,1]` fact gives this.
* **`secondLimit_fails_free` — the N+ for the sibling mechanism of F-6**: over
  `DP ∪ Ax(freeUI) ∪ Ax(freeUI')`, `P∞(∼u ⋏ ⋀_{i≤m} inst i) ≥ ε > 0` uniformly in `m`, while
  every instance is undecided (`free2_inst_lt_one`: `P∞(inst c) < 1`). In every completed world
  `u'` entails every instance, and `∼u ⋏ u'` is the finite `Ax`-consistent conjunction Soto's
  "only through quantification" overlooks.

**Block override.** `famWorld v g` overrides a world on the whole family-`9` block (payload `p`
gets `g p`); on family-`9`-free sentences it agrees with `v` (`famWorld_holds_of_free`, FAF's
`holds_congr_atomCodes`). The paper instantiations (`ui_free_paper`,
`secondLimit_fails_free_paper`, and their `_lia` forms at FAF's own inductor) discharge the
freeness premise by `bli-found`'s `paperDP_cleanroomFree`.

**Not shown**: that the bound of `secondLimit_fails_free` can fail for some inductor without the
sibling. That would need an inductor with a prescribed limit, not a criterion theorem; what is
shown is that with free instances `u'` is the only sentence of the process entailing them all
(`⊤` no longer does), so `secondLimit_fails_generic`'s hypothesis `himp'` is exercised.
-/

namespace Cleanroom.Bli.BliRvcUi

open LogicalInduction LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Propositional Filter Topology
  Cleanroom.Bli.BliFound

/-! ## The free families and the block override -/

section Family

/-- **The free UI family**: universal-role atom `freshAtom 9 ⟨1, 0⟩`, instance atoms
`freshAtom 9 ⟨2, c⟩` — pairwise distinct fresh atoms no base process mentions, tied only by the
schema.
Source: mandate T3.3; audit r1 (fix accepted for fidelity B2 / adversarial issue 1)
Kind: D
Fidelity: exact (schema 1 on free instance atoms) -/
def freeUI : UIFamily where
  u := freshAtom 9 (Nat.pair 1 0)
  inst c := freshAtom 9 (Nat.pair 2 c)

/-- **The sibling**: `u' := freshAtom 9 ⟨1, 1⟩` with the same free instances (plays `∀m(φ ∧ φ)`:
syntactically distinct, same instances).
Source: mandate T3.7; audit r1 (fix accepted for fidelity B1 / adversarial issue 2)
Kind: D
Fidelity: exact -/
def freeUI' : UIFamily where
  u := freshAtom 9 (Nat.pair 1 1)
  inst c := freshAtom 9 (Nat.pair 2 c)

/-- The free instance family is primitive recursive (an atom whose code is a `Nat.pair` tower).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freeUI_inst_prim : Primrec freeUI.inst := by
  have h : freeUI.inst = fun c =>
      (Formula.atom (Nat.pair (cleanroomBaseTag + 9) (Nat.pair 2 c)) : Sentence) := rfl
  rw [h]
  exact sentenceAtom_prim.comp (Primrec₂.natPair.comp (Primrec.const _)
    (Primrec₂.natPair.comp (Primrec.const 2) Primrec.id))

/-- `freeUI'` has the same instances.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freeUI'_inst_prim : Primrec freeUI'.inst := freeUI_inst_prim

/-- Override a world on the whole family-`9` block: the fresh atom with payload `p` gets `g p`,
every other atom keeps the world's value.
Source: none: infrastructure (`setAtom` is the one-atom version; bli-found's `Extend.override`
the schedule-wide one)
Kind: D
Fidelity: n/a -/
def famWorld (v : PCWorld) (g : ℕ → Prop) : PCWorld := fun a =>
  (∃ p, a = freshAtomCode 9 p ∧ g p) ∨ ((∀ p, a ≠ freshAtomCode 9 p) ∧ v a)

/-- The override holds the family-`9` atom of payload `p` iff `g p`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma famWorld_holds_fresh (v : PCWorld) (g : ℕ → Prop) (p : ℕ) :
    (famWorld v g).Holds (freshAtom 9 p) ↔ g p := by
  rw [freshAtom, PCWorld.holds_atom]
  constructor
  · rintro (⟨p', hp', hg⟩ | ⟨hne, -⟩)
    · obtain ⟨-, rfl⟩ := freshAtomCode_inj.mp hp'
      exact hg
    · exact absurd rfl (hne p)
  · intro hg
    exact Or.inl ⟨p, rfl, hg⟩

/-- On a sentence mentioning no family-`9` atom the override agrees with the world.
Source: none: infrastructure (FAF `PCWorld.holds_congr_atomCodes`)
Kind: L
Fidelity: n/a -/
lemma famWorld_holds_of_free (v : PCWorld) (g : ℕ → Prop) {φ : Sentence}
    (hφ : ∀ p, freshAtomCode 9 p ∉ sentenceAtomCodes φ) :
    (famWorld v g).Holds φ ↔ v.Holds φ :=
  PCWorld.holds_congr_atomCodes φ fun a ha => by
    have hne : ∀ p, a ≠ freshAtomCode 9 p := fun p h => hφ p (by rw [← h]; exact ha)
    show ((∃ p, a = freshAtomCode 9 p ∧ g p) ∨ ((∀ p, a ≠ freshAtomCode 9 p) ∧ v a)) ↔ v a
    constructor
    · rintro (⟨p, hp, -⟩ | ⟨-, hv⟩)
      · exact absurd hp (hne p)
      · exact hv
    · intro hv
      exact Or.inr ⟨hne, hv⟩

/-- A world consistent with a family-`9`-free stage stays consistent after the block override.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma famWorld_consistentWith {v : PCWorld} {D : Finset Sentence} (hv : v.ConsistentWith D)
    (hfree : ∀ φ ∈ D, ∀ p, freshAtomCode 9 p ∉ sentenceAtomCodes φ) (g : ℕ → Prop) :
    (famWorld v g).ConsistentWith D := fun φ hφ =>
  (famWorld_holds_of_free v g (hfree φ hφ)).mpr (hv φ hφ)

end Family

/-! ## Over any family-`9`-free base -/

section Generic

variable {DP : DeductiveProcess}
  (hfree : ∀ n, ∀ φ ∈ DP.D n, ∀ p, freshAtomCode 9 p ∉ sentenceAtomCodes φ)
  (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))

/-- The base augmented with the schema for `freeUI`.
Source: mandate T3.3
Kind: D
Fidelity: exact -/
abbrev freeDP (DP : DeductiveProcess) : DeductiveProcess := DP.union (AxProcess freeUI)

/-- The base augmented with both schemas (`u` and its sibling `u'`).
Source: mandate T3.7
Kind: D
Fidelity: exact -/
abbrev freeDP2 (DP : DeductiveProcess) : DeductiveProcess :=
  (DP.union (AxProcess freeUI)).union (AxProcess freeUI')

include hfree in
/-- A block override whose values satisfy the schema (`g ⟨1,0⟩ → g ⟨2,i⟩`) is consistent with every
stage of `freeDP DP` whose base stage the world was consistent with.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma famWorld_consistentWith_free {v : PCWorld} {n : ℕ} (hv : v.ConsistentWith (DP.D n))
    (g : ℕ → Prop) (h1 : g (Nat.pair 1 0) → ∀ i, g (Nat.pair 2 i)) :
    (famWorld v g).ConsistentWith ((freeDP DP).D n) := by
  rw [PCWorld.consistentWith_union_iff]
  refine ⟨famWorld_consistentWith hv (hfree n) g, ?_⟩
  rw [consistentWith_axProcess_iff]
  intro i _ hu
  have hu' : g (Nat.pair 1 0) := (famWorld_holds_fresh v g (Nat.pair 1 0)).mp hu
  exact (famWorld_holds_fresh v g (Nat.pair 2 i)).mpr (h1 hu' i)

include hfree in
/-- The same for both schemas.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma famWorld_consistentWith_free2 {v : PCWorld} {n : ℕ} (hv : v.ConsistentWith (DP.D n))
    (g : ℕ → Prop) (h1 : g (Nat.pair 1 0) → ∀ i, g (Nat.pair 2 i))
    (h2 : g (Nat.pair 1 1) → ∀ i, g (Nat.pair 2 i)) :
    (famWorld v g).ConsistentWith ((freeDP2 DP).D n) := by
  rw [PCWorld.consistentWith_union_iff]
  refine ⟨famWorld_consistentWith_free hfree hv g h1, ?_⟩
  rw [consistentWith_axProcess_iff]
  intro i _ hu
  have hu' : g (Nat.pair 1 1) := (famWorld_holds_fresh v g (Nat.pair 1 1)).mp hu
  exact (famWorld_holds_fresh v g (Nat.pair 2 i)).mpr (h2 hu' i)

include hfree hworld in
/-- `hworld` for `freeDP DP` (the all-true block).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem freeDP_hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((freeDP DP).D n) := fun n =>
  let ⟨v, hv⟩ := hworld n
  ⟨famWorld v (fun _ => True), famWorld_consistentWith_free hfree hv _ (fun _ _ => trivial)⟩

include hfree hworld in
/-- `hworld` for `freeDP2 DP`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem freeDP2_hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((freeDP2 DP).D n) := fun n =>
  let ⟨v, hv⟩ := hworld n
  ⟨famWorld v (fun _ => True),
    famWorld_consistentWith_free2 hfree hv _ (fun _ _ => trivial) (fun _ _ => trivial)⟩

include hfree hworld in
/-- **T3.3's non-vacuity witness (N+)**: for every inductor over `DP ∪ Ax(freeUI)`,
`0 < P∞(u) < P∞(inst c) < 1` for every `c`. Both sides are interior and the inequality is strict,
so `ui_limit_of_union`'s conclusion is a constraint the schema forces, not a `[0,1]` fact: the
all-true block gives `P∞(u) > 0`; the block "`u` false, `inst c` false" gives `P∞(inst c) < 1`;
the block "`u` false, everything else true" gives `P∞(inst c ⋏ ∼u) > 0`, and the schema gives
`P∞(u ⋏ ∼inst c) = 0`, hence strictness (`limitingBelief_lt_of_theory_imp`).
Source: mandate T3.3 (b); [[bli-program-desiderata]] P8, D-UI; audit r1 (fidelity B2, adversarial
issue 1)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem ui_free_nontrivial {P : History} [IsLogicalInductor P (freeDP DP)] (c : ℕ) :
    0 < limitingBelief P freeUI.u ∧
    limitingBelief P freeUI.u < limitingBelief P (freeUI.inst c) ∧
    limitingBelief P (freeUI.inst c) < 1 := by
  have hw := freeDP_hworld hfree hworld
  refine ⟨?_, ?_, ?_⟩
  · refine limitingBelief_pos_of_nonDogmatism hw fun n => ?_
    obtain ⟨v, hv⟩ := hworld n
    exact ⟨famWorld v (fun _ => True),
      famWorld_consistentWith_free hfree hv _ (fun _ _ => trivial),
      (famWorld_holds_fresh v _ (Nat.pair 1 0)).mpr trivial⟩
  · refine limitingBelief_lt_of_theory_imp hw (fun v hv hu =>
      holds_imp_of_consistentWithTheory_ax (PCWorld.consistentWithTheory_union_right hv) c hu)
      fun n => ?_
    obtain ⟨v, hv⟩ := hworld n
    refine ⟨famWorld v (fun p => p ≠ Nat.pair 1 0),
      famWorld_consistentWith_free hfree hv _ (fun h => (h rfl).elim), ?_⟩
    rw [PCWorld.holds_and, PCWorld.holds_neg]
    refine ⟨(famWorld_holds_fresh v _ (Nat.pair 2 c)).mpr ?_,
      fun h => (famWorld_holds_fresh v _ (Nat.pair 1 0)).mp h rfl⟩
    intro h
    exact absurd (Nat.pair_eq_pair.mp h).1 (by norm_num)
  · refine limitingBelief_lt_one_of_nonDogmatism hw fun n => ?_
    obtain ⟨v, hv⟩ := hworld n
    refine ⟨famWorld v (fun p => p ≠ Nat.pair 1 0 ∧ p ≠ Nat.pair 2 c),
      famWorld_consistentWith_free hfree hv _ (fun h => (h.1 rfl).elim), ?_⟩
    intro h
    exact ((famWorld_holds_fresh v _ (Nat.pair 2 c)).mp h).2 rfl

include hfree hworld in
/-- **Over both schemas the instances stay undecided**: `P∞(inst c) < 1` for every `c` (the block
"`u`, `u'`, `inst c` false" is consistent with every stage). So the sibling family is not the
degenerate one of `secondLimit_fails_ax`, where the instances are theorems of the base.
Source: audit r1 (fidelity B1, adversarial issue 2)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem free2_inst_lt_one {P : History} [IsLogicalInductor P (freeDP2 DP)] (c : ℕ) :
    limitingBelief P (freeUI.inst c) < 1 := by
  refine limitingBelief_lt_one_of_nonDogmatism (freeDP2_hworld hfree hworld) fun n => ?_
  obtain ⟨v, hv⟩ := hworld n
  refine ⟨famWorld v (fun p => p ≠ Nat.pair 1 0 ∧ p ≠ Nat.pair 1 1 ∧ p ≠ Nat.pair 2 c),
    famWorld_consistentWith_free2 hfree hv _ (fun h => (h.1 rfl).elim)
      (fun h => (h.2.1 rfl).elim), ?_⟩
  intro h
  exact ((famWorld_holds_fresh v _ (Nat.pair 2 c)).mp h).2.2 rfl

include hfree hworld in
/-- **T3.7 (b) — the sibling mechanism, isolated (N+)**: over `DP ∪ Ax(freeUI) ∪ Ax(freeUI')`,
with the instances free atoms (`free2_inst_lt_one`), `P∞(∼u ⋏ ⋀_{i≤m} inst i) ≥ ε > 0` uniformly
in `m`: the block "`u` false, `u'` true, all instances true" is consistent with every stage, and
`u'` entails every instance in every completed world. `∼u ⋏ u'` is the finite, `Ax`-consistent
conjunction entailing infinitely many instances that Soto's "only through quantification" rules
out (F-6). Unlike `secondLimit_fails_ax`, `⊤` does not entail the instances here, so the sibling
is the mechanism, not a bystander.
Source: bli-soto-a-2-006; Soto PDF 07 p. 2; [[bli-program-desiderata]] P8 (iii); audit r1
(fidelity B1, adversarial issue 2)
Kind: N+
Fidelity: exact (criterion level, limiting belief)
Hyps: (a) -/
theorem secondLimit_fails_free {P : History} [IsLogicalInductor P (freeDP2 DP)] :
    ∃ ε : ℝ, 0 < ε ∧ ∀ m, ε ≤ limitingBelief P (∼freeUI.u ⋏ instConj freeUI.inst m) :=
  secondLimit_fails_generic (freeDP2_hworld hfree hworld) (u := freeUI.u) (u' := freeUI'.u)
    (inst := freeUI.inst)
    (fun v hv hu' i =>
      holds_imp_of_consistentWithTheory_ax (PCWorld.consistentWithTheory_union_right hv) i hu')
    (fun n => by
      obtain ⟨v, hv⟩ := hworld n
      refine ⟨famWorld v (fun p => p ≠ Nat.pair 1 0),
        famWorld_consistentWith_free2 hfree hv _ (fun h => (h rfl).elim)
          (fun _ i h => absurd (Nat.pair_eq_pair.mp h).1 (by norm_num)), ?_⟩
      rw [PCWorld.holds_and, PCWorld.holds_neg]
      exact ⟨fun h => (famWorld_holds_fresh v _ (Nat.pair 1 0)).mp h rfl,
        (famWorld_holds_fresh v _ (Nat.pair 1 1)).mpr
          fun h => absurd (Nat.pair_eq_pair.mp h).2 (by norm_num)⟩)

end Generic

/-! ## At FAF's paper market -/

section Paper

variable (T : ArithmeticTheory) [T.Δ₁]

/-- `paperDP T` never mentions a family-`9` atom.
Source: bli-found `paperDP_cleanroomFree`
Kind: L
Fidelity: n/a -/
lemma paperDP_free9 :
    ∀ n, ∀ φ ∈ (paperDP T).D n, ∀ p, freshAtomCode 9 p ∉ sentenceAtomCodes φ :=
  fun n φ hφ p => (paperDP_cleanroomFree T n φ hφ).freshAtomCode_notMem 9 p

/-- `paperDP T ∪ Ax(freeUI)`.
Source: mandate T3.3
Kind: D
Fidelity: exact -/
noncomputable abbrev paperFree : DeductiveProcess := freeDP (paperDP T)

/-- `paperDP T ∪ Ax(freeUI) ∪ Ax(freeUI')`.
Source: mandate T3.7
Kind: D
Fidelity: exact -/
noncomputable abbrev paperFree2 : DeductiveProcess := freeDP2 (paperDP T)

/-- `paperFree T` is computable.
Source: mandate T3.1/T3.3
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem paperFree_computable : ComputableDeductiveProcess (paperFree T) :=
  union_ax_computable (paperDP_computable T) _ freeUI_inst_prim

/-- `paperFree2 T` is computable.
Source: mandate T3.7
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem paperFree2_computable : ComputableDeductiveProcess (paperFree2 T) :=
  union_ax_computable (paperFree_computable T) _ freeUI'_inst_prim

variable [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- **T3.3's N+ at the paper market**: `0 < P∞(u) < P∞(inst c) < 1` for every inductor over
`paperDP T ∪ Ax(freeUI)`.
Source: mandate T3.3 (b); audit r1 (fidelity B2, adversarial issue 1)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem ui_free_paper {P : History} [IsLogicalInductor P (paperFree T)] (c : ℕ) :
    0 < limitingBelief P freeUI.u ∧
    limitingBelief P freeUI.u < limitingBelief P (freeUI.inst c) ∧
    limitingBelief P (freeUI.inst c) < 1 :=
  ui_free_nontrivial (paperDP_free9 T) (paperDP_hworld T) c

/-- **T3.3's N+ at FAF's own inductor** `liaHistory (paperFree T)`.
Source: mandate T3.3 ("over `P := liaHistory (paperDP T ∪ AxProcess F)`")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem ui_free_paper_lia (c : ℕ) :
    0 < limitingBelief (liaHistory (paperFree T)) freeUI.u ∧
    limitingBelief (liaHistory (paperFree T)) freeUI.u <
      limitingBelief (liaHistory (paperFree T)) (freeUI.inst c) ∧
    limitingBelief (liaHistory (paperFree T)) (freeUI.inst c) < 1 :=
  haveI := LIA_is_logical_inductor (paperFree T) (paperFree_computable T)
  ui_free_paper T c

/-- The free instances are undecided over `paperFree2 T`.
Source: audit r1 (fidelity B1, adversarial issue 2)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem free2_inst_lt_one_paper {P : History} [IsLogicalInductor P (paperFree2 T)] (c : ℕ) :
    limitingBelief P (freeUI.inst c) < 1 :=
  free2_inst_lt_one (paperDP_free9 T) (paperDP_hworld T) c

/-- **T3.7 (b) at the paper market, sibling isolated (N+)**: over any inductor over
`paperDP T ∪ Ax(freeUI) ∪ Ax(freeUI')`, `P∞(∼u ⋏ ⋀_{i≤m} inst i) ≥ ε > 0` uniformly in `m`, with
every instance undecided (`free2_inst_lt_one_paper`).
Source: bli-soto-a-2-006; Soto PDF 07 p. 2; audit r1 (fidelity B1, adversarial issue 2)
Kind: N+
Fidelity: exact (criterion level, limiting belief)
Hyps: (a) -/
theorem secondLimit_fails_free_paper {P : History} [IsLogicalInductor P (paperFree2 T)] :
    ∃ ε : ℝ, 0 < ε ∧ ∀ m, ε ≤ limitingBelief P (∼freeUI.u ⋏ instConj freeUI.inst m) :=
  secondLimit_fails_free (paperDP_free9 T) (paperDP_hworld T)

/-- **T3.7 (b), sibling isolated, at FAF's own inductor** `liaHistory (paperFree2 T)`.
Source: mandate T3.7
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem secondLimit_fails_free_paper_lia :
    ∃ ε : ℝ, 0 < ε ∧ ∀ m, ε ≤ limitingBelief (liaHistory (paperFree2 T))
      (∼freeUI.u ⋏ instConj freeUI.inst m) :=
  haveI := LIA_is_logical_inductor (paperFree2 T) (paperFree2_computable T)
  secondLimit_fails_free_paper T

end Paper

end Cleanroom.Bli.BliRvcUi
