import Cleanroom.Li.LiPseudorandom.Market

/-!
# Audit round 3 (adversarial) — probe: the T7 reduction `starDP_computable ← truthStar_computable`
needs no FAF API addition at the delay-one profile

The package's open list, findings K5(iv) and report § FAF API requests item 4 say that reducing
`starDP_computable` (`ComputableDeductiveProcess (atomDP a (truthStar a g q) g)`) to
`truthStar_computable` (`Computable (truthStar a g q)`) needs "a `Computable` analogue of FAF's
`encode_stage_prim_of_list` / `ComputableDeductiveProcess.ofEncodePrim`" — filed as an FAF API
request. FAF's `Construction/DeductiveDovetail.lean` proves `prefixProcess_computable` (a prefix
process with a merely *computable* clause family is a `ComputableDeductiveProcess`) ten lines
below `ofEncodePrim`, by a `Computable.nat_rec` recursion; its proof transfers verbatim to
`atomDP a x (·+1)`, whose stage `n` is the list of the first `n` literals (`atomDP_succ_stage`).

This probe: `atomDP_succ_computable_of_computable` (the `Computable` analogue of the package's
`atomDP_succ_computable`), and the reduction `starDP_succ_computable_of_truthStar` /
`truthStar_succ_isLogicalInductor_of_truthStar`, from FAF as it stands. Not imported by the
library.
-/

namespace Cleanroom.Li.LiPseudorandom

open LogicalInduction LO.Propositional

/-- The first `n` literals, newest first (FAF's `prefixListRev` shape, for `List.range n`). -/
private def litListRev (ψ : ℕ → Sentence) : ℕ → List Sentence
  | 0 => []
  | k + 1 => ψ k :: litListRev ψ k

private lemma litListRev_eq (ψ : ℕ → Sentence) (n : ℕ) :
    litListRev ψ n = ((List.range n).map ψ).reverse := by
  induction n with
  | zero => rfl
  | succ k ih => rw [litListRev, ih]; simp [List.range_succ]

/-- The literal map is computable when the placement and the stream are (the `Computable`
analogue of the package's `literalOf_prim`). -/
theorem literalOf_computable {a : ℕ → ℕ} {x : ℕ → Bool} (ha : Computable a) (hx : Computable x) :
    Computable (literalOf a x) :=
  (Computable.cond hx (atom_prim.to_comp.comp ha) (negAtom_prim.to_comp.comp ha)).of_eq
    (fun j => by cases h : x j <;> simp [literalOf, h])

/-- **The delay-one process over merely computable data is a computable deductive process.**
FAF's `prefixProcess_computable` proof, transferred: the stage list by `Computable.nat_rec`,
its code by `encode_toFinset_eq`. No new FAF lemma is used. -/
theorem atomDP_succ_computable_of_computable {a : ℕ → ℕ} {x : ℕ → Bool}
    (ha : Computable a) (hx : Computable x) :
    ComputableDeductiveProcess (atomDP a x (fun j => j + 1)) := by
  have hψ : Computable (literalOf a x) := literalOf_computable ha hx
  have hrev : Computable (litListRev (literalOf a x)) := by
    have hstep : Computable fun p : ℕ × List Sentence => literalOf a x p.1 :: p.2 :=
      Computable.list_cons.comp (hψ.comp Computable.fst) Computable.snd
    refine (Computable.nat_rec Computable.id (Computable.const [])
      (hstep.comp₂ Computable.snd.to₂)).of_eq (fun k => ?_)
    induction k with
    | zero => rfl
    | succ k ih => simpa [litListRev] using ih
  have hlist : Computable fun n : ℕ => (List.range n).map (literalOf a x) :=
    (Computable.list_reverse.comp hrev).of_eq fun n => by
      rw [litListRev_eq, List.reverse_reverse]
  have hkey : Computable fun n => Encodable.encode
      ((List.dedup ((List.range n).map (literalOf a x))).insertionSort sentenceCodeLE) :=
    Computable.encode.comp
      ((sentenceInsertionSort_prim.comp dedup_prim).to_comp.comp hlist)
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hkey)
  refine ⟨code, fun n => ?_⟩
  rw [hcode, atomDP_succ_stage]
  exact Part.mem_some_iff.mpr (encode_toFinset_eq ((List.range n).map (literalOf a x)))

/-- **The reduction at the delay-one profile**: `starDP_computable` at `g = succ` follows from
`truthStar_computable` at `g = succ` with FAF as it stands. -/
theorem starDP_succ_computable_of_truthStar (a : ℕ → ℕ) (ha : Computable a) (q : ℚ)
    (h : Computable (truthStar a (fun j => j + 1) (q : ℝ))) :
    ComputableDeductiveProcess
      (atomDP a (truthStar a (fun j => j + 1) (q : ℝ)) (fun j => j + 1)) :=
  atomDP_succ_computable_of_computable ha h

/-- The inductor certificate at the delay-one profile, from `truthStar_computable` alone. -/
theorem truthStar_succ_isLogicalInductor_of_truthStar (a : ℕ → ℕ) (ha : Computable a) (q : ℚ)
    (h : Computable (truthStar a (fun j => j + 1) (q : ℝ))) :
    IsLogicalInductor (liaHistory (atomDP a (truthStar a (fun j => j + 1) (q : ℝ)) (fun j => j + 1)))
      (atomDP a (truthStar a (fun j => j + 1) (q : ℝ)) (fun j => j + 1)) :=
  LIA_is_logical_inductor _ (starDP_succ_computable_of_truthStar a ha q h)

end Cleanroom.Li.LiPseudorandom

#print axioms Cleanroom.Li.LiPseudorandom.atomDP_succ_computable_of_computable
#print axioms Cleanroom.Li.LiPseudorandom.truthStar_succ_isLogicalInductor_of_truthStar
