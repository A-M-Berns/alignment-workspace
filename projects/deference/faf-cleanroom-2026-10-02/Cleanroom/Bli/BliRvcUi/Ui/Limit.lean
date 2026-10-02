import Cleanroom.Bli.BliRvcUi.Ui.Defs
import Cleanroom.Bli.BliRvcUi.Limit

/-!
# `bli-rvc-ui` · Ui/Limit: universal instantiation for every inductor over the augmented process (T3.3, T3.7)

**T3.3 (load-bearing).** For any `[IsLogicalInductor P (DP.union (AxProcess F))]` with FAF's
`hworld`: (a) the day-`n` implication `u 🡒 inst n` is priced `→ 1` (`lic_provind_true`: it lies in
stage `n`, hence holds in every completed world; the e.c. certificate `hec` is the family's own
and is discharged for the witness families in `Ui/Paper.lean`); (b) `UILimit P F` — every
`u 🡒 inst c` holds in every completed world, so `P∞(u) ≤ P∞(inst c)` by semantic monotonicity of
the limiting belief. No `AsympLE` per-day claim is made here: the per-day form
`P_n(u) ≲ₙ P_n(inst c)` is stated as **OPEN** (`ui_perDay_open`), with the route through FAF's
`PolySequence.affine_provind_theory_le` on the fixed combination `u − inst c` (its value is `≤ 0` in
every completed world; what is missing is a `PolySequence` certificate for a fixed two-term
combination, which FAF does not provide and this package did not build).

**T3.7 (a), propositional.** The two-sided clause `UITwoSided` is unsatisfiable as soon as one
instance is priced `→ 1` and another `→ 0`: it would force `P_n(inst c₁) − P_n(inst c₂) → 0`. The
N+ over `paperDP T` is `Ui/Paper.lean`.

**T3.7 (b), generic.** If a sibling universal-role sentence `u'` implies every instance in every
completed world, and the world "`u` false, `u'` true" stays consistent with every stage, then
`P∞(∼u ⋏ ⋀_{i≤m} inst i) ≥ ε > 0` uniformly in `m` — Soto's second limit inequality fails. The
N+ is `Ui/Paper.lean`.
-/

namespace Cleanroom.Bli.BliRvcUi

open LogicalInduction LO.Propositional Filter Topology

/-! ## T3.3 — UI in the limit over the augmented process -/

section Union

variable {P : History} {DP : DeductiveProcess} {F : UIFamily}
  [IsLogicalInductor P (DP.union (AxProcess F))]
  (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.union (AxProcess F)).D n))
include hworld

/-- **T3.3 (a)**: the day-`n` schema implication is priced `→ 1`.
Source: mandate T3.3 (a); Soto PDF 07 Step 1; bli-soto-a-054
Kind: C
Fidelity: exact
Hyps: (a) `hec` is the family's e.c. certificate (discharged for the witnesses) -/
theorem ui_imp_limit_one (hec : MachineSentenceCodes fun n => F.u 🡒 F.inst n) :
    (fun n => P n (F.u 🡒 F.inst n)) ≈ₙ fun _ => 1 :=
  lic_provind_true P _ _ hec
    (fun n _ hv => hv.holds_of_mem_stage
      ⟨n, Finset.mem_union_right _ (imp_mem_axProcess F le_rfl)⟩) hworld

/-- **T3.3 (b) — universal instantiation in the limit** (load-bearing): over the augmented process
every inductor's limiting belief satisfies `P∞(∀x φ) ≤ P∞(φ(c))` for every `c`.
Source: mandate T3.3 (b); [[bli-program-desiderata]] P8, D-UI; [[bli-program-construction]] U8;
bli-soto-a-054 ("universal instantiation for free")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem ui_limit_of_union : UILimit P F := fun c =>
  limitingBelief_le_of_theory_imp hworld fun _ hv =>
    holds_imp_of_consistentWithTheory_ax (PCWorld.consistentWithTheory_union_right hv) c

omit [IsLogicalInductor P (DP.union (AxProcess F))] hworld in
/-- **F-19 — when every instance is believed, UI in the limit is vacuous**: `UILimit P F` follows
from `P∞(inst c) = 1` for all `c` and `P∞ ∈ [0,1]` alone — over *any* process, with no schema
and nothing about `u`. Together with `holds_of_limitingBelief_eq_one` (such instances hold in
every completed world, so every `u 🡒 inst c` does too, whatever `u`), this says a family
exhibiting T3.5 ("all instances believed, universal `< 1`") can never be a non-degenerate witness
of T3.3, and conversely: the two targets need different witnesses (`ui_strict_fresh` for the
first, `ui_free_nontrivial` for the second). Not a package theorem about UI; the evidence for the
regrading in repair round 1 (audit r1 probe `UiLimitTrivial`).
Source: audit r1 (both lenses); [[bli-rvc-ui-findings]] F-19
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem uiLimit_of_inst_limit_one {DP' : DeductiveProcess} [IsLogicalInductor P DP']
    (hworld' : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP'.D n)) (G : UIFamily)
    (h1 : ∀ c, limitingBelief P (G.inst c) = 1) : UILimit P G := fun c => by
  rw [h1 c]
  exact (limitingBelief_mem_Icc hworld' G.u).2

/-- **OPEN — the per-day form of UI over the augmented process**: `P_n(∀x φ) ≲ₙ P_n(φ(c))`.
Route: FAF's `PolySequence.affine_provind_theory_le` on the fixed affine combination
`u − inst c` (value `≤ 0` in every completed world of the union; prices in `[0,1]` bound it;
magnitude `2`), which needs a `PolySequence` certificate for a fixed two-term combination —
FAF has `sentenceAffine_polySequence` for one-share families only, and this package did not
build the two-term certificate. Alternative route: `lic_provind_false` on `u ⋏ ∼inst c` plus
asymptotic additivity, which needs the same machinery.
Source: mandate T3.3 ("state it as a separate OPEN row")
Kind: OPEN
Fidelity: exact
Hyps: (a) -/
theorem ui_perDay_open (c : ℕ) : (fun n => P n F.u) ≲ₙ fun n => P n (F.inst c) := by
  sorry

end Union

/-! ## T3.7 (a) — two-sided UI is unsatisfiable -/

/-- **`twoSided_ui_unsat`** (bli-paper-2-026; X9): the two-sided clause forces every pair of
instances to have asymptotically equal prices, so it is refuted by one instance priced `→ 1` and
one priced `→ 0`.
Source: bli-paper-2-026; [[bli-program-construction]] X9; [[bli-program-desiderata]] I14
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem twoSided_ui_unsat {P : History} {F : UIFamily} (h : UITwoSided P F) {c₁ c₂ : ℕ}
    (h1 : (fun n => P n (F.inst c₁)) ≈ₙ fun _ => 1)
    (h0 : (fun n => P n (F.inst c₂)) ≈ₙ fun _ => 0) : False := by
  have hA := (h c₁).sub (h c₂)
  have hB := h0.sub h1
  have hfun : (fun n => (P n F.u - P n (F.inst c₁)) - (P n F.u - P n (F.inst c₂)))
      = fun n => P n (F.inst c₂) - P n (F.inst c₁) := by
    funext n; ring
  have hA' : (fun n => P n (F.inst c₂) - P n (F.inst c₁)) ≈ₙ fun _ => (0 : ℝ) := by
    rw [← hfun]
    simpa using hA
  have hC : (fun _ => (0 : ℝ)) ≈ₙ fun _ => (0 : ℝ) - 1 := hA'.symm.trans hB
  unfold AsympEq at hC
  have := tendsto_nhds_unique hC tendsto_const_nhds
  norm_num at this

/-! ## T3.7 (b) — the second limit inequality fails, generically -/

/-- The finite conjunction of the instances `inst 0, …, inst m`.
Source: Soto PDF 07 p. 2 (`⋀_{i ≤ m} φ(i)`)
Kind: D
Fidelity: exact -/
def instConj (inst : ℕ → Sentence) (m : ℕ) : Sentence :=
  sentenceConjunction ((List.range (m + 1)).map inst)

/-- `holds_instConj`.
Source: none: infrastructure (FAF `PCWorld.holds_sentenceConjunction`)
Kind: L
Fidelity: n/a -/
lemma holds_instConj (v : PCWorld) (inst : ℕ → Sentence) (m : ℕ) :
    v.Holds (instConj inst m) ↔ ∀ i ≤ m, v.Holds (inst i) := by
  unfold instConj
  rw [holds_sentenceConjunction]
  simp only [List.mem_map, List.mem_range]
  constructor
  · intro h i hi
    exact h _ ⟨i, by omega, rfl⟩
  · rintro h φ ⟨i, hi, rfl⟩
    exact h i (by omega)

/-- **Soto's second limit inequality fails, generically**: with a sibling universal-role sentence
`u'` implying every instance in every completed world, and the world "`u` false, `u'` true"
consistent with every stage, `P∞(∼u ⋏ ⋀_{i≤m} inst i)` stays `≥ ε > 0` for every `m` — the
limit over `m` is not `0`.
Source: bli-soto-a-2-006 (refutation of PDF 07 p. 2's "we also get the other inequality");
[[bli-program-desiderata]] P8 (iii)
Kind: C
Fidelity: exact (stated at the criterion level, for the limiting belief)
Hyps: (a) -/
theorem secondLimit_fails_generic {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) {u u' : Sentence}
    {inst : ℕ → Sentence}
    (himp' : ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds u' → ∀ i, v.Holds (inst i))
    (hnd : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds (∼u ⋏ u')) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ m, ε ≤ limitingBelief P (∼u ⋏ instConj inst m) := by
  refine ⟨limitingBelief P (∼u ⋏ u'), limitingBelief_pos_of_nonDogmatism hworld hnd, fun m => ?_⟩
  refine limitingBelief_le_of_theory_imp hworld fun v hv h => ?_
  rw [PCWorld.holds_and] at h ⊢
  refine ⟨h.1, ?_⟩
  rw [holds_instConj]
  intro i _
  exact himp' v hv h.2 i

end Cleanroom.Bli.BliRvcUi
