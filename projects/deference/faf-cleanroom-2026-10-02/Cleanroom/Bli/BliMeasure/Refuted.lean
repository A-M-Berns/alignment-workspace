import Cleanroom.Bli.BliMeasure.Witness
import Cleanroom.Bli.BliMeasure.Lic

/-!
# `bli-measure` · Refuted: `bli-found`'s full-scope constraints fail for B3 of record (target 2,
the refutations; repair round 1)

Over `paperDP 𝗜𝚺₁`, the recursion of record and its denominator mesh (`paperBase ov`,
`paperMesh ov` — the package's own N+ setting), `bli-found`'s `E1r`, `E1x`, `E2x`, `E3` and `E4`
on their full scopes are **refuted**, and with them `RespectsPast` and `IsBLI_AppB`. The instance is
one sentence: the realized day-`0` state's atom `φ := ⌜𝑸_0 = actual 0⌝` (`paperPhi0`). It is a
candidate's state atom (`b3Actual_mem`), large on day `0`, and small on some later day `n`
(`paperPhi0_exists_day`, from `smallOn_tokenSize`). On that day:

* B3 prices it at `1` — the realized-past convention (`b3Bits_past`), which is what exact `TB`
  needs on day `n+1`'s own atom (`b3History_paperPhi0`);
* the base prices it by its world measure `w n`, which has full support on the stage's
  consistent worlds (`recBase_fullSupport`), and the stage is state-tag-free
  (`paperDP_tagFree`), so the world with that atom flipped to `false` is consistent, charged, and
  the marginal is `≠ 1` (`Q_paperPhi0_ne_one`).

So: `paper_E1x_refuted` (`E1x` on the denominator mesh — the mesh on which the state-free part is
exact, `b3_E1x_denom_stateFree`), `paper_E1r_refuted` (on it `E1r` and `E1x` coincide,
`measureRound_denomMesh`), `paper_E4_refuted` (balance: the right-hand side of `E4` is the rounded
measure's marginal of `φ`, `sum_superbelief_val_eq`, which is `≠ 1`), `paper_respectsPast_refuted`
(by the package's own `b3_E1x_denom_of_respectsPast`, contrapositive — so the conditional rows
`b3_E1r_of_respectsPast` / `b3_E1x_denom_of_respectsPast` are **vacuous at the instantiation of
record**; they are inhabited only by a base run over `bliDP`, the fixpoint of `bli-assemble`'s
`Fixpoint.lean`, which is a different object and is not constructed), `paper_isBLI_AppB_refuted`
(its `E1r` conjunct), `paper_obstructionE1x_refuted` (obstruction (ii) of target 7 is **not** the
mesh: exact small agreement fails on the past state atoms on every mesh), and `paper_E2x_refuted`
(`bli-found`'s `E2x` at `Sminus (n+1) (n+1)` scope: the point-mass candidate at the extension of a
consistent world reading `φ` as `false` is charged by the face kernel
(`candidate_charged_of_support`), its value of `φ` is `0`, while `𝐏_n(φ ⋏ σ) = 𝐏_n(σ) > 0` because
every charged B3 world holds the realized past literal — a proved instance of finding F2 (b) on a
**past** state atom; the case of a *future* atom `n < k < m` (a candidate's fixed opinion versus
the chain's backward conditional) remains argued, not proved), and `paper_E3_refuted` (`bli-found`'s
`E3` at `Sminus (n+1) (n+1)` scope with `o := n+2`: `q₁` the realized day-`(n+1)` state, `q₂` the
charged point-mass candidate one day later, and the two-step mass `𝐏_n(σ₁ ⋏ σ₂) = 𝐏_{n+1}(σ₂) ·
𝐏_n(σ₁) > 0` by exact `TB` (`b3_TB`) with the conjuncts swapped (`b3History_and_comm`); added by
the repair's continuation agent, 2026-10-02).

These are findings about the mandate's design (its "definitional `E1r` on `smallSet n`" is false
for the object it specifies, because the base of record is run over `DP`, not over `bliDP`), not
defects of the proved theorems: the state-free rows (`IsBLI_B3`) are the rows of record. Origin:
audit round 1 (adversarial) B1, whose probe `run/wp/bli-measure/audit-r1-probes/E1xRefuted.lean`
this module carries into the package. Everything here is conditional on `bli-coherent-mm`:
computability open.
-/

namespace Cleanroom.Bli.BliMeasure

open LogicalInduction LO.Propositional Finset BoolPCWorld Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliFound Cleanroom.Bli.BliOverlay Cleanroom.Bli.BliCoherentMm
  Cleanroom.Bli.BliTrajectory

/-! ## The sentence: the realized day-`0` state's atom -/

/-- The atom code of the realized day-`0` state's atom (a candidate's state atom: `b3Actual_mem`).
Source: none: infrastructure (audit r1 adversarial B1)
Kind: D
Fidelity: n/a -/
noncomputable abbrev paperA0 (ov : Overlay) : ℕ :=
  freshAtomCode stateFamily (Nat.pair 0 (b3Actual (paperBase ov) (paperMesh ov) 0))

/-- The realized day-`0` state's atom, as a sentence (`= Formula.atom (paperA0 ov)` by `rfl`).
Source: none: infrastructure (audit r1 adversarial B1)
Kind: D
Fidelity: n/a -/
noncomputable abbrev paperPhi0 (ov : Overlay) : Sentence :=
  stateAtom 0 (b3Actual (paperBase ov) (paperMesh ov) 0)

/-- The atom carries the state tag.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma unpair_paperA0 (ov : Overlay) : (Nat.unpair (paperA0 ov)).1 = stateTag := by
  unfold paperA0 freshAtomCode
  rw [Nat.unpair_pair]

/-- A day `n > 0` on which the atom is small (every sentence is small from its token size on).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma paperPhi0_exists_day (ov : Overlay) : ∃ n, 0 < n ∧ paperPhi0 ov ∈ smallSet n :=
  ⟨tokenSize (paperPhi0 ov) + 1, Nat.succ_pos _,
    smallSet_mono (Nat.le_succ _) (mem_smallSet.mpr (smallOn_tokenSize _))⟩

/-- The atom is within the bound on any day on which it is small.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma paperA0_lt_B (ov : Overlay) {n : ℕ} (hφ : paperPhi0 ov ∈ smallSet n) :
    paperA0 ov < (paperBase ov).𝔅.B n :=
  lt_of_lt_of_le (Nat.lt_succ_self _)
    (show atomBound (Formula.atom (paperA0 ov)) ≤ _ from (paperBase ov).𝔅.B_cover n _ hφ)

/-- A stage-consistent world that reads the atom `false` (tag-freeness of the paper process, as
in `paper_two_consistent` — here at a *candidate's* state atom, not the non-candidate atom `90`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma paper_exists_consistent_false (ov : Overlay) {n : ℕ} (ha : paperA0 ov < (paperBase ov).𝔅.B n) :
    ∃ u : FiniteWorld ((paperBase ov).𝔅.B n),
      (worldOf u).ConsistentWith ((paperDP 𝗜𝚺₁).D n) ∧ u.toBoolPCWorld (paperA0 ov) = false := by
  classical
  obtain ⟨v, hv⟩ := paperDP_hcons n
  set B := (paperBase ov).𝔅.B n
  let u₁ : FiniteWorld B := FiniteWorld.restrict (ofPCWorld v) B
  let i : Fin B := ⟨paperA0 ov, ha⟩
  let u₂ : FiniteWorld B := Function.update u₁ i false
  have hfree := paperDP_tagFree 𝗜𝚺₁ (le_refl stateTag)
  have hu₁ : (worldOf u₁).ConsistentWith ((paperDP 𝗜𝚺₁).D n) := by
    intro φ hφ
    exact (holds_worldOf_restrict v ((paperBase ov).B_stage n φ hφ)).mpr (hv φ hφ)
  have hu₂ : (worldOf u₂).ConsistentWith ((paperDP 𝗜𝚺₁).D n) := by
    intro φ hφ
    have hφfree := hfree n φ hφ
    have hagree : ∀ a ∈ sentenceAtomCodes φ, (worldOf u₁) a ↔ (worldOf u₂) a := by
      intro a ha'
      have hne : a ≠ paperA0 ov := by
        intro h'
        apply hφfree a ha'
        rw [h']
        exact unpair_paperA0 ov
      show u₁.toBoolPCWorld a = true ↔ u₂.toBoolPCWorld a = true
      unfold FiniteWorld.toBoolPCWorld
      split_ifs with ha''
      · have : (⟨a, ha''⟩ : Fin B) ≠ i := fun h => hne (congrArg Fin.val h)
        simp only [u₂, Function.update_of_ne this]
      · exact Iff.rfl
    exact (PCWorld.holds_congr_atomCodes φ hagree).mp (hu₁ φ hφ)
  refine ⟨u₂, hu₂, ?_⟩
  unfold FiniteWorld.toBoolPCWorld
  rw [dif_pos ha]
  simp only [u₂, i, Function.update_self]

/-- A world charged by the base's day-`n` measure that reads the atom `false` (full support).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma paper_exists_charged_false (ov : Overlay) {n : ℕ} (ha : paperA0 ov < (paperBase ov).𝔅.B n) :
    ∃ u : FiniteWorld ((paperBase ov).𝔅.B n),
      (paperBase ov).w n u ≠ 0 ∧ u.toBoolPCWorld (paperA0 ov) = false := by
  obtain ⟨u, hu, hbit⟩ := paper_exists_consistent_false ov ha
  exact ⟨u, recBase_fullSupport _ ov paperDP_hcons n u hu, hbit⟩

/-- **B3 prices the realized day-`0` state's atom at `1`** on every day on which it is small (the
realized-past convention, `b3Bits_past`, at horizon `0`).
Source: none: infrastructure (audit r1 adversarial B1)
Kind: L
Fidelity: n/a -/
lemma b3History_paperPhi0 (ov : Overlay) {n : ℕ}
    (hφ : stateAtom 0 (b3Actual (paperBase ov) (paperMesh ov) 0) ∈ smallSet n) :
    b3History (paperBase ov) (paperMesh ov) n
      (stateAtom 0 (b3Actual (paperBase ov) (paperMesh ov) 0)) = 1 := by
  rw [b3History_eq _ _ (covers_zero_of_small _ _ hφ), b3Mass_zero]
  have hev : ∀ u' : FiniteWorld ((paperBase ov).𝔅.B n),
      eval (b3Bits (paperBase ov) (paperMesh ov) n 0 PUnit.unit u'.toBoolPCWorld)
        (stateAtom 0 (b3Actual (paperBase ov) (paperMesh ov) 0)) = true := by
    intro u'
    rw [eval_b3Bits_stateAtom,
      b3Bits_past _ _ (sysState_of_mem _ _ (b3Actual_mem (paperBase ov) (paperMesh ov) 0)) (Nat.zero_le n)]
    exact decide_eq_true rfl
  have hsum : ∑ u : FiniteWorld ((paperBase ov).𝔅.B n),
      measureRound (paperBase ov) (paperMesh ov) n u *
        (if eval (b3Bits (paperBase ov) (paperMesh ov) n 0 PUnit.unit u.toBoolPCWorld)
            (stateAtom 0 (b3Actual (paperBase ov) (paperMesh ov) 0)) then (1 : ℚ) else 0) = 1 := by
    calc _ = ∑ u : FiniteWorld ((paperBase ov).𝔅.B n), measureRound (paperBase ov) (paperMesh ov) n u := by
          apply Finset.sum_congr rfl
          intro u _
          rw [if_pos (hev u), mul_one]
      _ = 1 := measureRound_sum _ _ n
  rw [hsum, Rat.cast_one]

/-- **The base prices the realized day-`0` state's atom `≠ 1`** on every day on which it is small
(a charged world reads it `false`; `respects_iff`).
Source: none: infrastructure (audit r1 adversarial B1)
Kind: L
Fidelity: n/a -/
lemma Q_paperPhi0_ne_one (ov : Overlay) {n : ℕ} (hφ : paperPhi0 ov ∈ smallSet n) :
    (paperBase ov).Q n (paperPhi0 ov) ≠ 1 := by
  intro hQ
  set base := paperBase ov
  obtain ⟨u, hu, hbit⟩ := paper_exists_charged_false ov (paperA0_lt_B ov hφ)
  rw [base.Q_eq n _ hφ] at hQ
  have hall := (respects_iff (base.w_nonneg n) (base.w_sum n) {paperPhi0 ov}).mp
    (fun ψ hψ => by rw [Finset.mem_singleton] at hψ; rw [hψ]; exact hQ) u hu (paperPhi0 ov)
    (Finset.mem_singleton_self _)
  have htrue : u.toBoolPCWorld (paperA0 ov) = true := hall
  rw [hbit] at htrue
  exact Bool.false_ne_true htrue

/-! ## Two facts about B3's coherence family -/

/-- **A stage sentence conjoins for free**: every world of B3's day-`n` coherence family holds the
B3 stage (`b3History_coherentOn`), so for `φ ∈ b3Stage n` and every `ψ`, `𝐏_n(φ ⋏ ψ) = 𝐏_n(ψ)`.
Source: none: infrastructure (the step shared by `paper_E2x_refuted` and `paper_E3_refuted`)
Kind: L
Fidelity: n/a -/
lemma b3History_and_of_mem_stage {DP : DeductiveProcess} (base : CoherentBase DP) (𝓜 : Mesh)
    (hfree : TagFreeProcess stateTag DP) (n : ℕ) {φ : Sentence} (hφ : φ ∈ b3Stage base 𝓜 n)
    (ψ : Sentence) : b3History base 𝓜 n (φ ⋏ ψ) = b3History base 𝓜 n ψ := by
  obtain ⟨k, W, w, hW, -, -, hp⟩ :=
    b3History_coherentOn base 𝓜 hfree n (sentenceAtomCodes (φ ⋏ ψ))
  rw [hp (φ ⋏ ψ) (Finset.Subset.refl _),
    hp ψ (by rw [sentenceAtomCodes_and]; exact Finset.subset_union_right)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hφi : (W i).Holds φ := hW i φ hφ
  unfold PCWorld.payout
  rw [PCWorld.holds_and]
  by_cases hψ : (W i).Holds ψ
  · rw [if_pos ⟨hφi, hψ⟩, if_pos hψ]
  · rw [if_neg (fun h => hψ h.2), if_neg hψ]

/-- **B3's prices are symmetric in the conjuncts** (the same coherence family prices both orders).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma b3History_and_comm {DP : DeductiveProcess} (base : CoherentBase DP) (𝓜 : Mesh)
    (n : ℕ) (φ ψ : Sentence) :
    b3History base 𝓜 n (φ ⋏ ψ) = b3History base 𝓜 n (ψ ⋏ φ) := by
  obtain ⟨k, W, w, -, -, -, hp⟩ :=
    b3History_coherentOn_empty base 𝓜 n (sentenceAtomCodes (φ ⋏ ψ))
  rw [hp (φ ⋏ ψ) (Finset.Subset.refl _),
    hp (ψ ⋏ φ) (by
      rw [sentenceAtomCodes_and, sentenceAtomCodes_and]
      exact Finset.union_subset Finset.subset_union_right Finset.subset_union_left)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  unfold PCWorld.payout
  rw [PCWorld.holds_and, PCWorld.holds_and]
  by_cases hφ : (W i).Holds φ <;> by_cases hψ : (W i).Holds ψ
  · rw [if_pos ⟨hφ, hψ⟩, if_pos ⟨hψ, hφ⟩]
  · rw [if_neg (fun h => hψ h.2), if_neg (fun h => hψ h.1)]
  · rw [if_neg (fun h => hφ h.1), if_neg (fun h => hφ h.2)]
  · rw [if_neg (fun h => hφ h.1), if_neg (fun h => hφ h.2)]

/-- The realized day-`0` state's atom is a B3 stage literal on every day (`stateLits`).
Source: none: infrastructure (audit r1 adversarial B1)
Kind: L
Fidelity: n/a -/
lemma paperPhi0_mem_b3Stage (ov : Overlay) (n : ℕ) :
    paperPhi0 ov ∈ b3Stage (paperBase ov) (paperMesh ov) n := by
  unfold b3Stage stateLits
  apply Finset.mem_union_right
  rw [Finset.mem_image]
  refine ⟨(stateFamily, Nat.pair 0 (b3Actual (paperBase ov) (paperMesh ov) 0), true), ?_, ?_⟩
  · rw [mem_stateEntries]
    exact ⟨0, by omega, Or.inl rfl⟩
  · rw [literalOf_true]
    rfl

/-- **Conjoining the realized day-`0` state's atom changes no B3 price**, on every day:
`𝐏_n(⌜𝑸_0 = actual 0⌝ ⋏ ψ) = 𝐏_n(ψ)` — every charged B3 world holds the realized past literal.
Source: none: infrastructure (audit r1 adversarial B1; the step shared by `paper_E2x_refuted` and
`paper_E3_refuted`)
Kind: L
Fidelity: n/a -/
lemma b3History_paperPhi0_and (ov : Overlay) (n : ℕ) (ψ : Sentence) :
    b3History (paperBase ov) (paperMesh ov) n (paperPhi0 ov ⋏ ψ) =
      b3History (paperBase ov) (paperMesh ov) n ψ :=
  b3History_and_of_mem_stage _ _ (paperDP_tagFree 𝗜𝚺₁ (le_refl stateTag)) n
    (paperPhi0_mem_b3Stage ov n) ψ

/-! ## The refutations -/

/-- **`bli-found`'s `E1x` is refuted** for B3 of record over the paper process on the denominator
mesh: on the day the realized day-`0` state's atom becomes small, B3 prices it `1` and the base
prices it `≠ 1`. Exact small agreement holds only on the state-free part
(`b3_E1x_denom_stateFree`); on past state atoms it fails on every mesh.
Source: [[bli-measure-mandate]] target 2 (`E1x` on the denominator mesh), target 7 (ii);
`bli-found` `E1x`; audit r1 adversarial B1
Kind: P
Fidelity: exact (the refuted predicate is `bli-found`'s, over the variant state system F1)
Hyps: (a) none (over the recursion of record; conditional on `bli-coherent-mm`: computability open) -/
theorem paper_E1x_refuted (ov : Overlay) :
    ¬ E1x (ratHistory (paperBase ov).Q) (b3History (paperBase ov) (paperMesh ov)) := by
  intro hE
  obtain ⟨n, -, hφ⟩ := paperPhi0_exists_day ov
  have h := (hE n _ hφ).symm.trans (b3History_paperPhi0 ov hφ)
  have h' : (((paperBase ov).Q n (paperPhi0 ov) : ℚ) : ℝ) = 1 := h
  exact Q_paperPhi0_ne_one ov hφ (by exact_mod_cast h')

/-- **`bli-found`'s `E1r` is refuted** for B3 of record over the paper process on the denominator
mesh (on it `E1r` and `E1x` coincide, `measureRound_denomMesh`): the mandate's "definitional
`E1r` on `smallSet n`" is false for the object it specifies.
Source: [[bli-measure-mandate]] target 2 (`E1r`); `bli-found` `E1r`; audit r1 adversarial B1
Kind: P
Fidelity: exact (the refuted predicate is `bli-found`'s, over the variant state system F1)
Hyps: (a) none -/
theorem paper_E1r_refuted (ov : Overlay) :
    ¬ E1r (b3StateSystem (paperBase ov) (paperMesh ov)) (b3History (paperBase ov) (paperMesh ov)) := by
  intro hE
  apply paper_E1x_refuted ov
  intro n φ hφ
  rw [hE n φ hφ, b3StateSystem_actual, b3StateSystem_val_actual, measureRound_denomMesh,
    ← (paperBase ov).Q_eq n φ hφ]
  rfl

/-- **`bli-found`'s `E4` (balance on all of `smallSet n`) is refuted** for B3 of record over the
paper process on the denominator mesh: the right-hand side at the realized day-`0` state's atom
is the rounded measure's marginal of it (`sum_superbelief_val_eq`), i.e. the base's price, `≠ 1`,
while B3 prices it `1`. Balance holds on the state-free part (`b3_E4_stateFree`).
Source: [[bli-measure-mandate]] target 2 (`E4`); `bli-found` `E4`; audit r1 adversarial §4
("not probed")
Kind: P
Fidelity: exact (the refuted predicate is `bli-found`'s, over the variant state system F1)
Hyps: (a) none -/
theorem paper_E4_refuted (ov : Overlay) :
    ¬ E4 (b3StateSystem (paperBase ov) (paperMesh ov)) (b3History (paperBase ov) (paperMesh ov)) := by
  intro hE
  obtain ⟨n, -, hφ⟩ := paperPhi0_exists_day ov
  have h := hE n _ hφ
  rw [sum_superbelief_val_eq (paperBase ov) (paperMesh ov) n ((paperBase ov).𝔅.B_cover n _ hφ),
    measureRound_denomMesh, ← (paperBase ov).Q_eq n _ hφ] at h
  have h' : (((paperBase ov).Q n (paperPhi0 ov) : ℚ) : ℝ) = 1 :=
    h.symm.trans (b3History_paperPhi0 ov hφ)
  exact Q_paperPhi0_ne_one ov hφ (by exact_mod_cast h')

/-- **`RespectsPast` is refuted at the instantiation of record** (not merely "not established"):
by the package's own `b3_E1x_denom_of_respectsPast`, contrapositive. The conditional rows
`b3_E1r_of_respectsPast` / `b3_E1x_denom_of_respectsPast` are therefore vacuous over the
recursion of record; a base that respects its realized past is the fixpoint base over `bliDP`
(`bli-assemble` `Fixpoint.lean`), a different object, not constructed here.
Source: [[bli-measure-findings]] F2; audit r1 adversarial B1
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem paper_respectsPast_refuted (ov : Overlay) : ¬ RespectsPast (paperBase ov) (paperMesh ov) :=
  fun hr => paper_E1x_refuted ov (b3_E1x_denom_of_respectsPast _ hr)

/-- **`bli-found`'s `IsBLI_AppB` is refuted** for B3 of record over the paper process on the
denominator mesh (its `E1r` conjunct fails; so do its `E2x`, `E3` and `E4` conjuncts,
`paper_E2x_refuted`, `paper_E3_refuted`, `paper_E4_refuted`). The bundle B3 satisfies is `IsBLI_B3`
(`paperB3_isBLI_B3`), the state-free variant.
Source: [[bli-measure-mandate]] target 2 (`IsBLI_AppB S P`); `bli-found` `IsBLI_AppB`; audit r1
adversarial B1
Kind: P
Fidelity: exact (the refuted predicate is `bli-found`'s, over the variant state system F1)
Hyps: (a) none -/
theorem paper_isBLI_AppB_refuted (ov : Overlay) :
    ¬ IsBLI_AppB (b3StateSystem (paperBase ov) (paperMesh ov)) (b3History (paperBase ov) (paperMesh ov)) :=
  fun h => paper_E1r_refuted ov h.1

/-- **Obstruction (ii) is false on the denominator mesh too**: exact small agreement with the base
fails there on the past state atoms, so the gap between B3 and `bli-transfer`'s L1 is not the
mesh but the realized-past convention (on every mesh); the mesh only adds a rounding error on the
state-free part (`b3_E1r_err`).
Source: [[bli-measure-mandate]] target 7 (ii); audit r1 adversarial B1, N7
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem paper_obstructionE1x_refuted (ov : Overlay) :
    ¬ ObstructionE1x (paperBase ov) (paperMesh ov) :=
  paper_E1x_refuted ov

/-- **`bli-found`'s `E2x` (scope `Sminus m m`) is refuted** for B3 of record over the paper process
on the denominator mesh, at `m := n + 1`, `φ := ⌜𝑸_0 = actual 0⌝` (a **past** state atom, small on
day `n`), and the charged point-mass candidate at the extension of a consistent world reading `φ`
as `false`: `𝐏_n(φ ⋏ σ_q) = 𝐏_n(σ_q) > 0` but `val (n+1) q φ · 𝐏_n(σ_q) = 0`. This is the proved
instance of finding F2 (b); the future-atom case (`n < k < m`) is argued there, not proved.
Source: [[bli-measure-mandate]] target 2 (`E2x`, "state `bli-found`'s `E2x S P` as the corollary");
`bli-found` `E2x`; [[bli-measure-findings]] F2 (b); audit r1 adversarial B1, fidelity N4
Kind: P
Fidelity: exact (the refuted predicate is `bli-found`'s, over the variant state system F1)
Hyps: (a) none -/
theorem paper_E2x_refuted (ov : Overlay) :
    ¬ E2x (b3StateSystem (paperBase ov) (paperMesh ov)) (b3History (paperBase ov) (paperMesh ov)) := by
  intro hE
  obtain ⟨n, -, hφ⟩ := paperPhi0_exists_day ov
  set base := paperBase ov
  set 𝓜 := paperMesh ov
  have hφm : paperPhi0 ov ∈ Sminus (n + 1) (n + 1) := by
    rw [mem_Sminus]
    refine ⟨mem_smallSet.mp (smallSet_mono (Nat.le_succ n) hφ), ?_⟩
    intro a ha
    have := atomDay_stateAtom 0 (b3Actual base 𝓜 0) a ha
    omega
  obtain ⟨u, hcons, hbit⟩ := paper_exists_consistent_false ov (paperA0_lt_B ov hφ)
  -- the point-mass candidate at the extension of `u`
  let v : FiniteWorld (base.𝔅.B (n + 1)) := extFW (base.𝔅.B_mono n) u
  have hQ : pointTable (n + 1) v ∈ cgrid base.𝔅 𝓜 (n + 1) :=
    pointTable_mem_cgrid base.𝔅 𝓜 (n + 1) v
  have hface : pointTable (n + 1) v ∈ faceGen (cgrid base.𝔅 𝓜 (n + 1)) (roundedTable base 𝓜 n) := by
    apply candidate_charged_of_support base 𝓜 (recBase_fullSupport _ ov paperDP_hcons n)
      (meshFine_denomMesh _ n) hQ
    intro u' hu'
    change vecOf (pointTable (n + 1) v) u' ≠ 0 at hu'
    rw [vecOf_pointTable] at hu'
    have : v = u' := by
      by_contra h
      rw [if_neg h] at hu'
      exact hu' rfl
    rw [← this]
    show (worldOf (restrFW (base.𝔅.B_mono n) (extFW (base.𝔅.B_mono n) u))).ConsistentWith _
    rw [restrFW_extFW]
    exact hcons
  have hq : wcode base.𝔅 𝓜 (n + 1) (pointTable (n + 1) v) ∈ wstates base.𝔅 𝓜 (n + 1) :=
    wcode_mem_wstates _ _ hQ
  -- the candidate is charged
  have hpos : 0 < superbelief (b3History base 𝓜) n (wcode base.𝔅 𝓜 (n + 1) (pointTable (n + 1) v)) := by
    rw [b3_FS base 𝓜 n hq, wdecode_wcode base.𝔅 𝓜 hQ]
    exact hface
  -- its value of `φ` is `0`
  have hval : (b3StateSystem base 𝓜).val (n + 1) (wcode base.𝔅 𝓜 (n + 1) (pointTable (n + 1) v))
      (paperPhi0 ov) = 0 := by
    rw [b3StateSystem_val, wdecode_wcode base.𝔅 𝓜 hQ]
    have : wMarginal (vecOf (pointTable (n + 1) v)) (paperPhi0 ov) = 0 := by
      unfold wMarginal
      apply Finset.sum_eq_zero
      intro u' _
      rw [vecOf_pointTable]
      by_cases h : v = u'
      · subst h
        rw [if_pos rfl, one_mul, payoutRat_eq_ite, if_neg]
        intro hh
        have htrue : v.toBoolPCWorld (paperA0 ov) = true := hh
        rw [toBoolPCWorld_extFW, hbit] at htrue
        exact Bool.false_ne_true htrue
      · rw [if_neg h, zero_mul]
    rw [this, Rat.cast_zero]
  -- `𝐏_n(φ ⋏ σ) = 𝐏_n(σ)`: every charged B3 world holds the realized past literal `φ`
  have hLHS : b3History base 𝓜 n (paperPhi0 ov ⋏ stateAtom (n + 1) (wcode base.𝔅 𝓜 (n + 1) (pointTable (n + 1) v))) =
      b3History base 𝓜 n (stateAtom (n + 1) (wcode base.𝔅 𝓜 (n + 1) (pointTable (n + 1) v))) := by
    obtain ⟨k, W, w, hW, -, -, hp⟩ := b3History_coherentOn base 𝓜
      (paperDP_tagFree 𝗜𝚺₁ (le_refl stateTag)) n
      (sentenceAtomCodes (paperPhi0 ov ⋏ stateAtom (n + 1) (wcode base.𝔅 𝓜 (n + 1) (pointTable (n + 1) v))))
    rw [hp (paperPhi0 ov ⋏ stateAtom (n + 1) (wcode base.𝔅 𝓜 (n + 1) (pointTable (n + 1) v)))
        (Finset.Subset.refl _),
      hp (stateAtom (n + 1) (wcode base.𝔅 𝓜 (n + 1) (pointTable (n + 1) v)))
        (by rw [sentenceAtomCodes_and]; exact Finset.subset_union_right)]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    have hφi : (W i).Holds (paperPhi0 ov) := by
      apply hW i
      show paperPhi0 ov ∈ b3Stage base 𝓜 n
      unfold b3Stage stateLits
      apply Finset.mem_union_right
      rw [Finset.mem_image]
      refine ⟨(stateFamily, Nat.pair 0 (b3Actual base 𝓜 0), true), ?_, ?_⟩
      · rw [mem_stateEntries]
        exact ⟨0, by omega, Or.inl rfl⟩
      · rw [literalOf_true]
        rfl
    unfold PCWorld.payout
    rw [PCWorld.holds_and]
    by_cases hψ : (W i).Holds (stateAtom (n + 1) (wcode base.𝔅 𝓜 (n + 1) (pointTable (n + 1) v)))
    · rw [if_pos ⟨hφi, hψ⟩, if_pos hψ]
    · rw [if_neg (fun h => hψ h.2), if_neg hψ]
  have hE' := hE n (n + 1) (Nat.lt_succ_self n) _ hq (paperPhi0 ov) hφm
  rw [hLHS, hval, zero_mul] at hE'
  unfold superbelief at hpos
  rw [hE'] at hpos
  exact lt_irrefl _ hpos

/-- **`bli-found`'s `E3` (scope `Sminus m m`, "latest state wins") is refuted** for B3 of record
over the paper process on the denominator mesh, at `m := n + 1`, `o := n + 2`,
`φ := ⌜𝑸_0 = actual 0⌝` (a **past** state atom, small on day `n`), `q₁ :=` the realized
day-`(n+1)` state and `q₂ :=` the charged point-mass candidate of day `n + 2` at the extension of a
consistent world reading `φ` as `false`:
`𝐏_n(φ ⋏ (σ₁ ⋏ σ₂)) = 𝐏_n(σ₁ ⋏ σ₂) = 𝐏_{n+1}(σ₂) · 𝐏_n(σ₁) > 0` (every charged B3 world holds the
realized past literal, `b3History_paperPhi0_and`; the two-step mass is a product by `b3_TB`;
`paper_realized_charged`; `candidate_charged_of_support` one day later), while
`val (n+2) q₂ φ · 𝐏_n(σ₁ ⋏ σ₂) = 0`. This is the "`E3` at `Sminus` scope: not probed" case of
finding F2 (b), now proved on a past atom; the future-atom case (`n < k < m`) stays argued, not
proved. `E3SF` (`b3_E3_stateFree`) is the row of record.
Source: [[bli-measure-mandate]] target 2 (`E3`); `bli-found` `E3`; [[bli-measure-findings]] F2 (b);
audit r1 adversarial §4 ("not probed"); repair round 1 (continuation)
Kind: P
Fidelity: exact (the refuted predicate is `bli-found`'s, over the variant state system F1)
Hyps: (a) none -/
theorem paper_E3_refuted (ov : Overlay) :
    ¬ E3 (b3StateSystem (paperBase ov) (paperMesh ov)) (b3History (paperBase ov) (paperMesh ov)) := by
  intro hE
  obtain ⟨n, -, hφ⟩ := paperPhi0_exists_day ov
  set base := paperBase ov
  set 𝓜 := paperMesh ov
  have hφ1 : paperPhi0 ov ∈ smallSet (n + 1) := smallSet_mono (Nat.le_succ n) hφ
  have hφm : paperPhi0 ov ∈ Sminus (n + 1) (n + 1) := by
    rw [mem_Sminus]
    refine ⟨mem_smallSet.mp hφ1, ?_⟩
    intro a ha
    have := atomDay_stateAtom 0 (b3Actual base 𝓜 0) a ha
    omega
  obtain ⟨u, hcons, hbit⟩ := paper_exists_consistent_false ov (paperA0_lt_B ov hφ1)
  -- the point-mass candidate of day `n + 2` at the extension of `u`
  let v : FiniteWorld (base.𝔅.B (n + 1 + 1)) := extFW (base.𝔅.B_mono (n + 1)) u
  have hQ : pointTable (n + 1 + 1) v ∈ cgrid base.𝔅 𝓜 (n + 1 + 1) :=
    pointTable_mem_cgrid base.𝔅 𝓜 (n + 1 + 1) v
  have hface : pointTable (n + 1 + 1) v ∈
      faceGen (cgrid base.𝔅 𝓜 (n + 1 + 1)) (roundedTable base 𝓜 (n + 1)) := by
    apply candidate_charged_of_support base 𝓜 (recBase_fullSupport _ ov paperDP_hcons (n + 1))
      (meshFine_denomMesh _ (n + 1)) hQ
    intro u' hu'
    change vecOf (pointTable (n + 1 + 1) v) u' ≠ 0 at hu'
    rw [vecOf_pointTable] at hu'
    have : v = u' := by
      by_contra h
      rw [if_neg h] at hu'
      exact hu' rfl
    rw [← this]
    show (worldOf (restrFW (base.𝔅.B_mono (n + 1)) (extFW (base.𝔅.B_mono (n + 1)) u))).ConsistentWith _
    rw [restrFW_extFW]
    exact hcons
  have hq₂ : wcode base.𝔅 𝓜 (n + 1 + 1) (pointTable (n + 1 + 1) v) ∈ wstates base.𝔅 𝓜 (n + 1 + 1) :=
    wcode_mem_wstates _ _ hQ
  -- `q₂` is charged from the realized day-`(n+1)` state: `0 < 𝐏_{n+1}(σ₂)`
  have hpos₂ : 0 < superbelief (b3History base 𝓜) (n + 1)
      (wcode base.𝔅 𝓜 (n + 1 + 1) (pointTable (n + 1 + 1) v)) := by
    rw [b3_FS base 𝓜 (n + 1) hq₂, wdecode_wcode base.𝔅 𝓜 hQ]
    exact hface
  -- the realized day-`(n+1)` state is charged: `0 < 𝐏_n(σ₁)`
  have hpos₁ : 0 < superbelief (b3History base 𝓜) n (b3Actual base 𝓜 (n + 1)) :=
    paper_realized_charged ov n
  -- `𝐏_n(σ₁ ⋏ σ₂) = 𝐏_{n+1}(σ₂) · 𝐏_n(σ₁)`: exact `TB` with the conjuncts swapped
  have hTB := b3_TB base 𝓜 n
    (stateAtom (n + 1 + 1) (wcode base.𝔅 𝓜 (n + 1 + 1) (pointTable (n + 1 + 1) v)))
  rw [b3StateSystem_actual] at hTB
  have hprod : b3History base 𝓜 n (stateAtom (n + 1) (b3Actual base 𝓜 (n + 1)) ⋏
      stateAtom (n + 1 + 1) (wcode base.𝔅 𝓜 (n + 1 + 1) (pointTable (n + 1 + 1) v))) =
      superbelief (b3History base 𝓜) (n + 1)
          (wcode base.𝔅 𝓜 (n + 1 + 1) (pointTable (n + 1 + 1) v)) *
        superbelief (b3History base 𝓜) n (b3Actual base 𝓜 (n + 1)) :=
    (b3History_and_comm base 𝓜 n _ _).trans hTB.symm
  -- `q₂`'s value of `φ` is `0`
  have hval : (b3StateSystem base 𝓜).val (n + 1 + 1)
      (wcode base.𝔅 𝓜 (n + 1 + 1) (pointTable (n + 1 + 1) v)) (paperPhi0 ov) = 0 := by
    rw [b3StateSystem_val, wdecode_wcode base.𝔅 𝓜 hQ]
    have : wMarginal (vecOf (pointTable (n + 1 + 1) v)) (paperPhi0 ov) = 0 := by
      unfold wMarginal
      apply Finset.sum_eq_zero
      intro u' _
      rw [vecOf_pointTable]
      by_cases h : v = u'
      · subst h
        rw [if_pos rfl, one_mul, payoutRat_eq_ite, if_neg]
        intro hh
        have htrue : v.toBoolPCWorld (paperA0 ov) = true := hh
        rw [toBoolPCWorld_extFW, hbit] at htrue
        exact Bool.false_ne_true htrue
      · rw [if_neg h, zero_mul]
    rw [this, Rat.cast_zero]
  -- `𝐏_n(φ ⋏ (σ₁ ⋏ σ₂)) = 𝐏_n(σ₁ ⋏ σ₂)`: every charged B3 world holds the realized past literal
  have hLHS : b3History base 𝓜 n (paperPhi0 ov ⋏ (stateAtom (n + 1) (b3Actual base 𝓜 (n + 1)) ⋏
      stateAtom (n + 1 + 1) (wcode base.𝔅 𝓜 (n + 1 + 1) (pointTable (n + 1 + 1) v)))) =
      b3History base 𝓜 n (stateAtom (n + 1) (b3Actual base 𝓜 (n + 1)) ⋏
        stateAtom (n + 1 + 1) (wcode base.𝔅 𝓜 (n + 1 + 1) (pointTable (n + 1 + 1) v))) :=
    b3History_paperPhi0_and ov n _
  -- `E3` at `(n, n+1, n+2, actual (n+1), q₂, φ)`
  have hE' := hE n (n + 1) (n + 1 + 1) (Nat.lt_succ_self n) (Nat.lt_succ_self (n + 1))
    (b3Actual base 𝓜 (n + 1)) (b3Actual_mem base 𝓜 (n + 1)) _ hq₂ (paperPhi0 ov) hφm
  rw [hLHS, hval, zero_mul, hprod] at hE'
  exact (mul_pos hpos₂ hpos₁).ne' hE'

end Cleanroom.Bli.BliMeasure
