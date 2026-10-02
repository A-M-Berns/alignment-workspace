import Cleanroom.Bli.BliRvcUi.Ui.Limit
import Cleanroom.Bli.BliRvcUi.Hm.Paper
import Cleanroom.Bli.BliFound.PaperInstances
import Cleanroom.Bli.BliFound.Extend
import Foundation.FirstOrder.Incompleteness.Second

/-!
# `bli-rvc-ui` · Ui/Paper: universal instantiation at FAF's paper market (T3.5–T3.7)

**The instance family of record.** Instances are FAF quotation literals of a total decider
(`trueInst T c := ⌜True(c)⌝`, `BooleanQuoteCode.ofComputable (ComputablePred.const True)`): each is
`T`-provable (Σ₁-completeness, FAF's `pos_complete`), enters some stage of `paperDP T`, holds in
every completed-theory world, and the family carries its own e.c. certificate
(`sentence_poly`) and is primitive recursive. This is the paper's "`T ⊢ ψ_c` for every `c`" in the
form FAF's process actually publishes, in place of the mandate's `paperPrimeDecompose ψ_c`
(whose e.c. certificate for a growing numeral FAF does not provide).

* **T3.5 — `ui_strict_fresh` (N−; regraded in repair round 1).** Universal-role sentence
  `u := freshAtom 9 ⟨0,0⟩` (a fresh atom no FAF process mentions), instances `trueInst T`, process
  `paperDP T ∪ AxProcess ⟨u, trueInst T⟩`. For every inductor over it: every instance is priced
  `→ 1` and has limiting belief `1`; `u` has limiting belief `< 1` (`lic_nonDogmatism_dual`: the
  override of any stage world with `u ↦ false` is consistent with every stage); `UILimit` holds;
  hence `P∞(u) < P∞(inst c)` for every `c`. **What this does not show** (audit r1, both lenses):
  the instances are theorems of the base, so the schema is inert in the limit and `UILimit` here
  is `P∞(u) ≤ 1` (`uiLimit_of_inst_limit_one`); the strictness is non-dogmatism of an atom no
  stage decides. The universal role of `u` is nominal, which is why the grade is N−. F-19 shows
  this is forced: "all instances believed" makes any schema inert. The N+ for T3.3 is
  `ui_free_nontrivial` (`Ui/Free.lean`, free instance atoms, `0 < P∞(u) < P∞(inst c) < 1`); the
  semantic T3.5 is `ui_strict_paper_open`.
* **T3.6 — `ui_limit_paperDP`.** For a genuine first-order universal `∀⁰ φ` and its numeral
  instances `φ/[‘↑c’]` (`paperUI φ`), `UILimit` holds for every inductor over `paperDP T`
  **without any `AxProcess`**: `T ⊢ ∀⁰ φ 🡒 φ/[‘↑c’]` is logic (Foundation's `specialize`),
  `paperTheoryDP` publishes its prime decomposition, and `holds_paperPrimeDecompose_imp` turns it
  into `u 🡒 inst c` in every completed world. Soto's Step 1 is redundant over a theory (F-6).
* **T3.7 (a) — `twoSided_ui_unsat_paper` (N+).** The two-sided clause fails for the family whose
  instances are the table facts of T4.6 (one true, one false) over any inductor over `paperDP T`.
* **T3.7 (b) — `secondLimit_fails_ax` (N−; regraded in repair round 1).** A sibling
  universal-role atom `u'` with the same instances: over `paperDP T ∪ Ax(u) ∪ Ax(u')` the world
  "`u` false, `u'` true, all instances true" is consistent with every stage (a completed-theory
  world of `paperDP T` overridden at two fresh atoms), so `P∞(∼u ⋏ ⋀_{i≤m} inst i) ≥ ε > 0` for
  every `m`. **But the sibling is inert here** (audit r1): the instances are theorems of the
  base, so `⊤` entails them all and the same bound holds over `paperAx T` with no `u'`. The
  mechanism at this family is "the theory proves every instance while `u` is undecided" — the
  semantic reason of F-6, not the sibling prime. The sibling mechanism is isolated with free
  instances in `secondLimit_fails_free` (`Ui/Free.lean`).
* **`ui_strict_paper_open` (OPEN).** The semantic strict witness with `paperUI` and Gödel II:
  Foundation's `consistent_unprovable` is importable (`T ⊬ ↑T.consistent` for `𝗜𝚺₁ ⪯ T`), but
  `T.consistent` is a `𝚷₁.Sentence` built by `HierarchySymbol.Semiformula.mkPi`, and the
  remaining plumbing (its shape as `∀⁰ φ`, provability of each instance, a model of `T + ∼Con(T)`
  fed to `paperDP_hworld_of_model`) is not done here.
-/

namespace Cleanroom.Bli.BliRvcUi

open LogicalInduction LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Propositional Filter Topology
  Cleanroom.Bli.BliFound

section Instances

variable (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]

/-- The quote code of the always-true decider.
Source: mandate T3.5 (instances "each `T`-provable")
Kind: D
Fidelity: n/a -/
noncomputable def trueQuote : BooleanQuoteCode T (fun _ => True) :=
  BooleanQuoteCode.ofComputable (ComputablePred.const True)

/-- **The instance family of record**: `⌜True(c)⌝`, the tag-`2` quotation literal at input `c`.
Source: mandate T3.5
Kind: D
Fidelity: variant: quotation literals of a total decider in place of `paperPrimeDecompose ψ_c`
(each is `T`-provable and process-published; the e.c. certificate is FAF's) -/
noncomputable def trueInst (c : ℕ) : Sentence := (trueQuote T).sentence c

/-- Every completed-theory world of `paperDP T` holds every instance.
Source: FAF `BooleanQuoteCode.reflected`
Kind: L
Fidelity: n/a -/
lemma trueInst_holds (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) (c : ℕ) :
    v.Holds (trueInst T c) :=
  ((trueQuote T).reflected (paperQuotationPresentation T) c v hv).mpr trivial

/-- Every instance enters some stage of `paperDP T`.
Source: FAF `quote_positive_enters`
Kind: L
Fidelity: n/a -/
lemma trueInst_enters (c : ℕ) : ∃ k, trueInst T c ∈ (paperDP T).D k :=
  (paperQuotationPresentation T).quote_positive_enters _ c ((trueQuote T).pos_complete c trivial)

omit [T.Δ₁] in
/-- The instance family is machine-metered (its own e.c. certificate).
Source: FAF `BooleanQuoteCode.sentence_poly`
Kind: L
Fidelity: n/a -/
lemma trueInst_machineCodes : MachineSentenceCodes (trueInst T) :=
  MachineSentenceCodes.ofPolySentenceCodes (trueQuote T).sentence_poly

omit [T.Δ₁] in
/-- The instance family is primitive recursive (an atom whose code is a `Nat.pair` tower).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma trueInst_prim : Primrec (trueInst T) := by
  have h : trueInst T = fun c => (Formula.atom (Nat.pair 2 (Nat.pair (Encodable.encode universalQuotePos)
      (Nat.pair (Encodable.encode universalQuoteNeg) (Nat.pair (trueQuote T).code c)))) : Sentence) :=
    rfl
  rw [h]
  exact sentenceAtom_prim.comp (Primrec₂.natPair.comp (Primrec.const 2)
    (Primrec₂.natPair.comp (Primrec.const _) (Primrec₂.natPair.comp (Primrec.const _)
      (Primrec₂.natPair.comp (Primrec.const _) Primrec.id))))

omit [T.Δ₁] in
/-- A fresh-atom code never occurs in an instance (tag `2` versus tag `≥ 9`).
Source: FAF `sentenceAtomCodes_quoteAtom`; bli-found `freshAtomCode_unpair`
Kind: L
Fidelity: n/a -/
lemma freshAtomCode_notMem_trueInst (f p c : ℕ) :
    freshAtomCode f p ∉ sentenceAtomCodes (trueInst T c) := by
  intro h
  have h' : freshAtomCode f p ∈ sentenceAtomCodes (quoteAtom (Nat.pair (trueQuote T).code c)) := h
  have := sentenceAtomCodes_quoteAtom _ _ h'
  simp only [freshAtomCode_unpair, cleanroomBaseTag] at this
  omega

omit [T.Δ₁] in
/-- The family `n ↦ u 🡒 trueInst T n` is machine-metered: the RPN block for `🡒` (tag `2`) is
built from `MachineSentenceCodes.const u` and `trueInst_machineCodes`, the way FAF's
`MachineSentenceCodes.and` builds `⋏`. (T3.3 (a)'s certificate `hec` for the witness family.)
Source: none: infrastructure (FAF `MachineSentenceCodes.and`, `parseRpn_block_head`)
Kind: L
Fidelity: n/a -/
lemma trueInst_machineCodes_imp (u : Sentence) :
    MachineSentenceCodes (fun n => u 🡒 trueInst T n) := by
  have hu := MachineSentenceCodes.const u
  -- FAF has no `MachineSentenceCodes.imp`, so the RPN block for `u 🡒 ψ` is built directly, as
  -- `MachineSentenceCodes.and` builds `⋏`: the head token `2` (the tag of `🡒`) followed by the
  -- blocks of `u` and `ψ`.
  obtain ⟨a, ha, hpa⟩ := hu
  obtain ⟨b, hb, hpb⟩ := trueInst_machineCodes T
  refine ⟨fun z => 2 :: (a z ++ b z),
    (((MachineTokenStream.const [2]).append ha).append hb).of_eq (fun z => by simp),
    fun z => ?_⟩
  have hlen : (2 :: (a z ++ b z)).length = (a z).length + (b z).length + 1 := by simp
  rw [hlen, parseRpn_cons]
  rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
  rw [parseRpn_block_head (hpa z) (b z) (by omega)]
  simp only [Option.bind_some]
  rw [parseRpn_mono (b z) (show (b z).length ≤ (a z).length + (b z).length by omega) (hpb z)]
  rfl

omit [𝗥₀ ⪯ T] in
/-- The base process never mentions a fresh atom.
Source: bli-found `paperDP_cleanroomFree`
Kind: L
Fidelity: n/a -/
lemma paperDP_free_of_fresh (f p : ℕ) :
    ∀ n, ∀ φ ∈ (paperDP T).D n, freshAtomCode f p ∉ sentenceAtomCodes φ :=
  fun n φ hφ => (paperDP_cleanroomFree T n φ hφ).freshAtomCode_notMem f p

end Instances

/-! ## T3.5 — the strict witness -/

section Strict

variable (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]

/-- **The T3.5 family**: universal-role atom `freshAtom 9 ⟨0, 0⟩` (family `9`, day `0`), instances
`trueInst T` (theorems of the base: the schema is inert in the limit, F-19).
Source: mandate T3.5 (registry: family `9` = UI universal atoms; the mandate said `7`, which `bli-transfer` now owns)
Kind: D
Fidelity: variant: instance family `trueInst` in place of `paperPrimeDecompose ψ_c` (F-14) -/
noncomputable def freshUI : UIFamily where
  u := freshAtom 9 (Nat.pair 0 0)
  inst := trueInst T

/-- The T3.5 process: `paperDP T` augmented with the schema for `freshUI T`.
Source: mandate T3.5
Kind: D
Fidelity: exact -/
noncomputable abbrev paperAx : DeductiveProcess := (paperDP T).union (AxProcess (freshUI T))

/-- The augmented process is computable.
Source: mandate T3.1/T3.5
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem paperAx_computable : ComputableDeductiveProcess (paperAx T) :=
  union_ax_computable (paperDP_computable T) _ (trueInst_prim T)

variable [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- Every stage of the augmented process admits a consistent world with `u` false.
Source: mandate T3.5 (route: override the fresh atom)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem paperAx_hworld_u_false :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperAx T).D n) ∧ ¬ v.Holds (freshUI T).u :=
  union_ax_hworld_u_false rfl (paperDP_free_of_fresh T 9 _) (paperDP_hworld T)

/-- `hworld` for the augmented process.
Source: mandate T3.5
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem paperAx_hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperAx T).D n) :=
  union_ax_hworld rfl (paperDP_free_of_fresh T 9 _) (paperDP_hworld T)

/-- **T3.5 — the fresh-atom witness (N−; regraded in repair round 1)**: for every inductor over
`paperDP T ∪ AxProcess (freshUI T)`, (i) the instances are priced `→ 1`, (ii) each has limiting
belief `1`, (iii) the universal-role atom has limiting belief `< 1`, (iv) `UILimit` holds, and
(v) `P∞(u) < P∞(inst c)` for every `c`. **What this shows and does not show** (audit r1, both
lenses): the instances are theorems of the base, so (ii) and (iv) are independent of `u` and of
the schema — `UILimit` here is `P∞(u) ≤ 1` (`uiLimit_of_inst_limit_one`) — and (iii) is
non-dogmatism of an atom no stage decides; the schema `u 🡒 inst c` is inert in the limit. So the
universal role of `u` is nominal: what is exhibited is "a sentence the process never decides stays
`< 1` while theorems go to `1`", the criterion-level mechanism of the Gödel case (bli-soto-a-082)
without its content (a genuine universal whose instances are its own numeral instances). That is
`ui_strict_paper_open` (OPEN). F-19 shows the degeneracy is forced: any family with all instances
believed has an inert schema, so T3.5's witness can never double as T3.3's; the N+ for
`ui_limit_of_union` is `ui_free_nontrivial` (`Ui/Free.lean`).
Source: mandate T3.5; bli-soto-a-082; [[bli-program-desiderata]] P8 ("strict somewhere")
Kind: N-
Fidelity: variant: instance family `trueInst` (F-14); the universal role is nominal (F-19)
Hyps: (a) -/
theorem ui_strict_fresh {P : History} [IsLogicalInductor P (paperAx T)] :
    ((fun n => P n ((freshUI T).inst n)) ≈ₙ fun _ => 1) ∧
    (∀ c, limitingBelief P ((freshUI T).inst c) = 1) ∧
    limitingBelief P (freshUI T).u < 1 ∧
    UILimit P (freshUI T) ∧
    ∀ c, limitingBelief P (freshUI T).u < limitingBelief P ((freshUI T).inst c) := by
  have hinst : ∀ c (v : PCWorld), v.ConsistentWithTheory (paperAx T) → v.Holds ((freshUI T).inst c) :=
    fun c v hv => trueInst_holds T v (consistentWithTheory_base_of_union hv) c
  have h1 : ∀ c, limitingBelief P ((freshUI T).inst c) = 1 := fun c =>
    limitingBelief_eq_one_of_theory (paperAx_hworld T) (hinst c)
  have hlt : limitingBelief P (freshUI T).u < 1 :=
    limitingBelief_lt_one_of_nonDogmatism (paperAx_hworld T) (paperAx_hworld_u_false T)
  refine ⟨?_, h1, hlt, ui_limit_of_union (paperAx_hworld T), fun c => ?_⟩
  · exact lic_provind_true P _ _ (trueInst_machineCodes T) (fun n v hv => hinst n v hv)
      (paperAx_hworld T)
  · rw [h1 c]
    exact hlt

/-- **T3.3 (a) discharged for the witness family**: the schema implications are priced `→ 1`.
Source: mandate T3.3 (a)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem paperAx_imp_limit_one {P : History} [IsLogicalInductor P (paperAx T)] :
    (fun n => P n ((freshUI T).u 🡒 (freshUI T).inst n)) ≈ₙ fun _ => 1 :=
  ui_imp_limit_one (paperAx_hworld T) (trueInst_machineCodes_imp T _)

/-- **T3.5's fresh-atom witness at FAF's own inductor** `liaHistory (paperAx T)` (N−, as
`ui_strict_fresh`: the schema is inert at this family).
Source: mandate T3.5 ("over `P := liaHistory (paperDP T ∪ AxProcess F)`")
Kind: N-
Fidelity: variant: instance family `trueInst` (F-14); the universal role is nominal (F-19)
Hyps: (a) -/
theorem ui_strict_fresh_lia :
    limitingBelief (liaHistory (paperAx T)) (freshUI T).u < 1 ∧
    UILimit (liaHistory (paperAx T)) (freshUI T) ∧
    ∀ c, limitingBelief (liaHistory (paperAx T)) (freshUI T).u <
      limitingBelief (liaHistory (paperAx T)) ((freshUI T).inst c) :=
  haveI := LIA_is_logical_inductor (paperAx T) (paperAx_computable T)
  let h := ui_strict_fresh T (P := liaHistory (paperAx T))
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

end Strict

/-! ## T3.6 — over `paperDP T`, universal instantiation needs no schema -/

section PaperUI

variable (T : ArithmeticTheory) [T.Δ₁]

/-- **The paper-facing family**: a first-order universal `∀⁰ φ` and its numeral instances
`φ/[‘↑c’]`, both as FAF's prime decompositions.
Source: mandate design decision 5 (`paperUI`); bli-paper-049
Kind: D
Fidelity: exact -/
noncomputable def paperUI (φ : ArithmeticSemisentence 1) : UIFamily where
  u := paperPrimeDecompose ((∀⁰ φ : ArithmeticSentence) : ArithmeticProposition)
  inst c := paperPrimeDecompose ((φ/[‘↑c’] : ArithmeticSentence) : ArithmeticProposition)

/-- A completed-theory world of `paperDP T` is one of `paperTheoryDP T`.
Source: FAF `paperDP` (a union with `paperTheoryDP T`)
Kind: L
Fidelity: n/a -/
lemma consistentWithTheory_paperTheoryDP_of_paperDP {v : PCWorld}
    (hv : v.ConsistentWithTheory (paperDP T)) : v.ConsistentWithTheory (paperTheoryDP T) :=
  fun n φ hφ => hv n φ (by
    rw [paperDP, DeductiveProcess.union_stage]
    exact Finset.mem_union_right _ hφ)

/-- **Universal instantiation holds in every completed world of `paperDP T`**: `T ⊢ ∀⁰ φ 🡒 φ/[c]`
is logic (`specialize`), `paperTheoryDP` publishes it, and the decomposition of an implication
is an implication in every world.
Source: mandate T3.6; FAF `holds_paperPrimeDecompose_of_provable`, `holds_paperPrimeDecompose_imp`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem paperUI_imp_holds (φ : ArithmeticSemisentence 1) (c : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.Holds (paperUI φ).u → v.Holds ((paperUI φ).inst c) := by
  have hprov : T ⊢ ∀⁰ φ 🡒 φ/[‘↑c’] := Theory.Proof.specialize φ ‘↑c’
  have h := PCWorld.holds_paperPrimeDecompose_of_provable T v
    (consistentWithTheory_paperTheoryDP_of_paperDP T hv) _ hprov
  have h2 : v.Holds (paperPrimeDecompose
      (((∀⁰ φ : ArithmeticSentence) : ArithmeticProposition) 🡒
        ((φ/[‘↑c’] : ArithmeticSentence) : ArithmeticProposition))) := by
    simpa using h
  exact (PCWorld.holds_paperPrimeDecompose_imp v _ _).mp h2

variable [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- **T3.6 — D-UI in the limit is a theorem of the criterion over `paperDP T`, with no schema
process** (Soto's Step 1 is redundant over a theory): for every inductor over `paperDP T` and every
`φ`, `P∞(∀⁰ φ) ≤ P∞(φ/[‘↑c’])` for every `c`.
Source: mandate T3.6; bli-soto-a-054; [[bli-program-desiderata]] D-UI, P8
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem ui_limit_paperDP {P : History} [IsLogicalInductor P (paperDP T)]
    (φ : ArithmeticSemisentence 1) : UILimit P (paperUI φ) := fun c =>
  limitingBelief_le_of_theory_imp (paperDP_hworld T) fun v hv => paperUI_imp_holds T φ c v hv

/-- **T3.6 at FAF's own inductor.**
Source: mandate T3.6
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem ui_limit_paperDP_lia (φ : ArithmeticSemisentence 1) :
    UILimit (liaHistory (paperDP T)) (paperUI φ) :=
  haveI := paperLIA T
  ui_limit_paperDP T φ

/-- **OPEN — the semantic strict witness.** There is a first-order universal, each of whose
numeral instances `T` proves, that `T` does not prove (Gödel II, Foundation's
`consistent_unprovable`), and for every inductor over `paperDP T` its limiting belief is `< 1`
while every instance's is `1`. What is missing: `T.consistent`'s shape as `∀⁰ φ`
(`HierarchySymbol.Semiformula.mkPi`), provability of each instance, and a model of `T + ∼Con(T)`
fed to `paperDP_hworld_of_model` for the `< 1` half.
Source: mandate T3.5 (`ui_strict_paper`); bli-soto-a-082
Kind: OPEN
Fidelity: exact
Hyps: (a) -/
theorem ui_strict_paper_open [𝗜𝚺₁ ⪯ T] :
    ∃ φ : ArithmeticSemisentence 1, (∀ c, T ⊢ (φ/[‘↑c’] : ArithmeticSentence)) ∧
      T ⊬ (∀⁰ φ : ArithmeticSentence) ∧
      ∀ (P : History) [IsLogicalInductor P (paperDP T)],
        limitingBelief P (paperUI φ).u < 1 ∧ ∀ c, limitingBelief P ((paperUI φ).inst c) = 1 := by
  sorry

end PaperUI

/-! ## T3.7 — the two refutations at the paper market -/

section Refutations

variable (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- The family whose instances are the table facts of T4.6: `⌜code 5 has index ≥ 1 in table c⌝`.
Its universal-role atom is a fresh atom with **no** schema link, deliberately: the refutation of
the two-sided clause uses only two instances with different limits, whatever `u` is, so an
unlinked `u` makes the refutation stronger, not weaker. Mandate §5's warning about unlinked
universal atoms (which is about `UIAt`/`UILimit` becoming vacuous) is waived here (audit r1 N4/(d)).
Source: mandate T3.7 (N+ for the two-sided refutation)
Kind: D
Fidelity: variant: unlinked universal-role atom (harmless for a refutation of `UITwoSided`) -/
noncomputable def tableUI : UIFamily where
  u := freshAtom 9 (Nat.pair 0 2)
  inst := hmSentence T (entryAtLeast_computable 5 1)

/-- **T3.7 (a) — two-sided UI is unsatisfiable at the paper market (N+)**: over any inductor over
`paperDP T`, the family `tableUI T` has one instance priced `→ 1` (the actual table) and one
priced `→ 0` (the flipped table), so `UITwoSided` fails.
Source: bli-paper-2-026; [[bli-program-construction]] X9; mandate T3.7
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem twoSided_ui_unsat_paper {P : History} [IsLogicalInductor P (paperDP T)] :
    ¬ UITwoSided P (tableUI T) := fun h =>
  twoSided_ui_unsat h (c₁ := actualTableCode) (c₂ := flippedTableCode)
    (lic_provind_true P _ (fun _ => hmSentence T (entryAtLeast_computable 5 1) actualTableCode)
      (MachineSentenceCodes.const _)
      (fun _ v hv => (hm_reflected T _ _ v hv).mpr entryAtLeast_actual) (paperDP_hworld T))
    (lic_provind_false P _ (fun _ => hmSentence T (entryAtLeast_computable 5 1) flippedTableCode)
      (MachineSentenceCodes.const _)
      (fun _ v hv => (PCWorld.holds_neg v _).mpr fun hh =>
        not_entryAtLeast_flipped ((hm_reflected T _ _ v hv).mp hh)) (paperDP_hworld T))

/-- The sibling family: universal-role atom `freshAtom 9 ⟨0, 1⟩` (plays `∀m(φ ∧ φ)`: syntactically
distinct, same instances).
Source: mandate T3.7 (`secondLimit_fails_ax`)
Kind: D
Fidelity: exact -/
noncomputable def freshUI' : UIFamily where
  u := freshAtom 9 (Nat.pair 0 1)
  inst := trueInst T

/-- The doubly augmented process `paperDP T ∪ Ax(u) ∪ Ax(u')`.
Source: mandate T3.7
Kind: D
Fidelity: exact -/
noncomputable abbrev paperAx2 : DeductiveProcess :=
  ((paperDP T).union (AxProcess (freshUI T))).union (AxProcess (freshUI' T))

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- `paperAx2` is computable.
Source: mandate T3.7
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem paperAx2_computable : ComputableDeductiveProcess (paperAx2 T) :=
  union_ax_computable (paperAx_computable T) _ (trueInst_prim T)

/-- **The world "`u` false, `u'` true, all instances true"** is consistent with every stage of
`paperAx2 T`: a completed-theory world of `paperDP T` overridden at the two fresh atoms.
Source: mandate T3.7 (the `Ax`-consistent world of bli-soto-a-2-006 (i))
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem paperAx2_world : ∃ v : PCWorld, v.ConsistentWithTheory (paperAx2 T) ∧
    ¬ v.Holds (freshUI T).u ∧ v.Holds (freshUI' T).u := by
  obtain ⟨v, hv⟩ := paperDP_nonvacuous T
  have hne : freshAtomCode 9 (Nat.pair 0 1) ∉ sentenceAtomCodes (Formula.atom (freshAtomCode 9 (Nat.pair 0 0))) := by
    rw [sentenceAtomCodes_atom, Finset.mem_singleton, freshAtomCode_inj, Nat.pair_eq_pair]
    omega
  refine ⟨setAtom (setAtom v (freshAtomCode 9 (Nat.pair 0 0)) False) (freshAtomCode 9 (Nat.pair 0 1))
    True, ?_, ?_, ?_⟩
  · intro n
    rw [PCWorld.consistentWith_union_iff, PCWorld.consistentWith_union_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact consistentWith_setAtom (consistentWith_setAtom (hv n) (paperDP_free_of_fresh T 9 _ n)
        False) (paperDP_free_of_fresh T 9 _ n) True
    · rw [consistentWith_axProcess_iff]
      intro i _ hu
      exact absurd hu (by
        show ¬ (setAtom (setAtom v _ False) _ True).Holds (Formula.atom (freshAtomCode 9 (Nat.pair 0 0)))
        rw [holds_setAtom_of_notMem _ _ _ hne, holds_atom_setAtom]
        exact id)
    · rw [consistentWith_axProcess_iff]
      intro i _ _
      show (setAtom (setAtom v _ False) _ True).Holds (trueInst T i)
      rw [holds_setAtom_of_notMem _ _ _ (freshAtomCode_notMem_trueInst T _ _ i),
        holds_setAtom_of_notMem _ _ _ (freshAtomCode_notMem_trueInst T _ _ i)]
      exact trueInst_holds T v hv i
  · show ¬ (setAtom (setAtom v _ False) _ True).Holds (Formula.atom (freshAtomCode 9 (Nat.pair 0 0)))
    rw [holds_setAtom_of_notMem _ _ _ hne, holds_atom_setAtom]
    exact id
  · show (setAtom (setAtom v _ False) _ True).Holds (Formula.atom (freshAtomCode 9 (Nat.pair 0 1)))
    rw [holds_atom_setAtom]
    trivial

/-- `hworld` for `paperAx2 T`.
Source: mandate T3.7
Kind: L
Fidelity: n/a -/
theorem paperAx2_hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperAx2 T).D n) := fun n =>
  let ⟨v, hv, _, _⟩ := paperAx2_world T
  ⟨v, hv n⟩

/-- **T3.7 (b) at the paper market with theorem instances (N−; regraded in repair round 1)**: over
any inductor over `paperDP T ∪ Ax(u) ∪ Ax(u')`, `P∞(∼u ⋏ ⋀_{i≤m} inst i) ≥ ε > 0` uniformly in
`m`, although `u 🡒 inst i` is in the process for every `i`. **The sibling is inert here** (audit
r1, both lenses): the instances `trueInst T` are theorems of the base, so `⊤` (or `∼u`) entails
them all and the same bound holds over `paperAx T` with no `u'` (probes `SiblingIdle`,
`SiblingFreePaper`). The mechanism at this family is "the theory proves every instance while `u`
is undecided" — the semantic reason F-6 attributes to Gödel over a theory. The sibling-prime
mechanism (a finite `Ax`-consistent conjunction `∼u ⋏ u'` entailing every instance, with the
instances themselves undecided) is isolated in `secondLimit_fails_free` (`Ui/Free.lean`).
Source: bli-soto-a-2-006; Soto PDF 07 p. 2; [[bli-program-desiderata]] P8 (iii)
Kind: N-
Fidelity: variant: theorem instances (F-14); the sibling does no work at this family
Hyps: (a) -/
theorem secondLimit_fails_ax {P : History} [IsLogicalInductor P (paperAx2 T)] :
    ∃ ε : ℝ, 0 < ε ∧ ∀ m, ε ≤ limitingBelief P (∼(freshUI T).u ⋏ instConj (trueInst T) m) :=
  secondLimit_fails_generic (paperAx2_hworld T) (u := (freshUI T).u) (u' := (freshUI' T).u)
    (inst := trueInst T)
    (fun v hv hu' i =>
      holds_imp_of_consistentWithTheory_ax (PCWorld.consistentWithTheory_union_right hv) i hu')
    (fun n =>
      let ⟨v, hv, hnu, hu'⟩ := paperAx2_world T
      ⟨v, hv n, by rw [PCWorld.holds_and, PCWorld.holds_neg]; exact ⟨hnu, hu'⟩⟩)

/-- **T3.7 (b) with theorem instances at FAF's own inductor** `liaHistory (paperAx2 T)` (N−, as
`secondLimit_fails_ax`: the sibling is inert at this family).
Source: mandate T3.7
Kind: N-
Fidelity: variant: theorem instances (F-14); the sibling does no work at this family
Hyps: (a) -/
theorem secondLimit_fails_ax_lia :
    ∃ ε : ℝ, 0 < ε ∧ ∀ m, ε ≤ limitingBelief (liaHistory (paperAx2 T))
      (∼(freshUI T).u ⋏ instConj (trueInst T) m) :=
  haveI := LIA_is_logical_inductor (paperAx2 T) (paperAx2_computable T)
  secondLimit_fails_ax T

end Refutations

end Cleanroom.Bli.BliRvcUi
