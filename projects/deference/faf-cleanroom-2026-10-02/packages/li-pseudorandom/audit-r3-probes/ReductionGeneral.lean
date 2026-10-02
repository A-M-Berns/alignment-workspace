import Cleanroom.Li.LiPseudorandom.Market

/-!
# Audit round 3 (adversarial) — probe: the T7 reduction for every computable delay profile

Companion of `Reduction.lean` (the delay-one case). For *any* computable `a`, `x`, `g`,
`atomDP a x g` is a `ComputableDeductiveProcess`: stage `n` is the `toFinset` of the list of
literals of the members `j ≤ n` with `g j ≤ n`, built by a `Computable.nat_rec` recursion
(Mathlib has no `Computable.list_filter`/`list_map`, so the list is built by hand, as FAF does for
`prefixProcess_computable`), and coded through FAF's `encode_toFinset_eq`. Hence
`starDP_computable` reduces to `truthStar_computable` for every computable `g`, with FAF and
Mathlib as they stand — no "`Computable` analogue of `encode_stage_prim_of_list`" is needed from
FAF. Not imported by the library.
-/

namespace Cleanroom.Li.LiPseudorandom

open LogicalInduction LO.Propositional

/-- The literal map is computable when the placement and the stream are. -/
private theorem literalOf_computable' {a : ℕ → ℕ} {x : ℕ → Bool} (ha : Computable a)
    (hx : Computable x) : Computable (literalOf a x) :=
  (Computable.cond hx (atom_prim.to_comp.comp ha) (negAtom_prim.to_comp.comp ha)).of_eq
    (fun j => by cases h : x j <;> simp [literalOf, h])

/-- The literals of the members `j < m` with `g j ≤ n`, newest first. -/
private def filtListRev (g : ℕ → ℕ) (ψ : ℕ → Sentence) (n : ℕ) : ℕ → List Sentence
  | 0 => []
  | k + 1 => if g k ≤ n then ψ k :: filtListRev g ψ n k else filtListRev g ψ n k

private lemma filtListRev_eq (g : ℕ → ℕ) (ψ : ℕ → Sentence) (n m : ℕ) :
    filtListRev g ψ n m =
      (((List.range m).filter (fun j => decide (g j ≤ n))).map ψ).reverse := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [filtListRev, ih, List.range_succ, List.filter_append, List.map_append,
      List.reverse_append]
    by_cases h : g k ≤ n
    · simp [h]
    · simp [h]

/-- Stage `n` of `atomDP a x g` as a list's `toFinset`. -/
private lemma atomDP_stage_list (a : ℕ → ℕ) (x : ℕ → Bool) (g : ℕ → ℕ) (n : ℕ) :
    (atomDP a x g).D n =
      (((List.range (n + 1)).filter (fun j => decide (g j ≤ n))).map (literalOf a x)).toFinset := by
  ext φ
  rw [mem_atomDP_iff, List.mem_toFinset, List.mem_map]
  simp only [List.mem_filter, List.mem_range, Nat.lt_succ_iff, decide_eq_true_eq]

/-- **`atomDP` over merely computable data, at any computable delay profile, is a computable
deductive process** — from FAF and Mathlib as they stand. -/
theorem atomDP_computable_of_computable {a : ℕ → ℕ} {x : ℕ → Bool} {g : ℕ → ℕ}
    (ha : Computable a) (hx : Computable x) (hg : Computable g) :
    ComputableDeductiveProcess (atomDP a x g) := by
  have hψ : Computable (literalOf a x) := literalOf_computable' ha hx
  have hle : Computable fun p : ℕ × ℕ => decide (p.1 ≤ p.2) := by
    have h : PrimrecRel fun a b : ℕ => a ≤ b := Primrec.nat_le
    unfold PrimrecRel PrimrecPred at h
    obtain ⟨_, h⟩ := h
    exact (h.of_eq (fun p => by first | rfl | (congr) | simp)).to_comp
  have hc : Computable fun q : ℕ × (ℕ × List Sentence) => decide (g q.2.1 ≤ q.1) :=
    (hle.comp (Computable.pair (hg.comp (Computable.fst.comp Computable.snd)) Computable.fst)).of_eq
      (fun q => rfl)
  have hstep : Computable fun q : ℕ × (ℕ × List Sentence) =>
      cond (decide (g q.2.1 ≤ q.1)) (literalOf a x q.2.1 :: q.2.2) q.2.2 :=
    Computable.cond hc
      (Computable.list_cons.comp (hψ.comp (Computable.fst.comp Computable.snd))
        (Computable.snd.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  have hrev : Computable fun n => filtListRev g (literalOf a x) n (n + 1) := by
    refine (Computable.nat_rec Primrec.succ.to_comp (Computable.const []) hstep.to₂).of_eq
      (fun n => ?_)
    show Nat.rec (motive := fun _ => List Sentence) []
      (fun y IH => cond (decide (g y ≤ n)) (literalOf a x y :: IH) IH) (n + 1) = _
    generalize n + 1 = m
    induction m with
    | zero => rfl
    | succ k ih =>
      simp only [Bool.cond_decide] at ih
      simp only [filtListRev, Bool.cond_decide]
      rw [ih]
  have hlist : Computable fun n : ℕ =>
      ((List.range (n + 1)).filter (fun j => decide (g j ≤ n))).map (literalOf a x) :=
    (Computable.list_reverse.comp hrev).of_eq fun n => by
      rw [filtListRev_eq, List.reverse_reverse]
  have hkey : Computable fun n => Encodable.encode
      ((List.dedup (((List.range (n + 1)).filter (fun j => decide (g j ≤ n))).map
        (literalOf a x))).insertionSort sentenceCodeLE) :=
    Computable.encode.comp
      ((sentenceInsertionSort_prim.comp dedup_prim).to_comp.comp hlist)
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hkey)
  refine ⟨code, fun n => ?_⟩
  rw [hcode, atomDP_stage_list]
  exact Part.mem_some_iff.mpr (encode_toFinset_eq _)

/-- **The reduction, for every computable delay profile**: `starDP_computable` follows from
`truthStar_computable` with FAF as it stands. -/
theorem starDP_computable_of_truthStar (a g : ℕ → ℕ) (ha : Computable a) (hg : Computable g)
    (q : ℚ) (h : Computable (truthStar a g (q : ℝ))) :
    ComputableDeductiveProcess (atomDP a (truthStar a g (q : ℝ)) g) :=
  atomDP_computable_of_computable ha h hg

/-- The inductor certificate, from `truthStar_computable` alone. -/
theorem truthStar_isLogicalInductor_of_truthStar (a g : ℕ → ℕ) (ha : Computable a)
    (hg : Computable g) (q : ℚ) (h : Computable (truthStar a g (q : ℝ))) :
    IsLogicalInductor (liaHistory (atomDP a (truthStar a g (q : ℝ)) g))
      (atomDP a (truthStar a g (q : ℝ)) g) :=
  LIA_is_logical_inductor _ (starDP_computable_of_truthStar a g ha hg q h)

end Cleanroom.Li.LiPseudorandom

#print axioms Cleanroom.Li.LiPseudorandom.atomDP_computable_of_computable
#print axioms Cleanroom.Li.LiPseudorandom.truthStar_isLogicalInductor_of_truthStar
