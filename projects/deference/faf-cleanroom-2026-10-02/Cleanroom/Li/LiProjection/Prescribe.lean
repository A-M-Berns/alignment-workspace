import Cleanroom.Li.LiProjection.Defs
import LogicalInduction.Construction.Primcodable
import LogicalInduction.Construction.Freeze.Oracle
import LogicalInduction.Construction.Freeze.Counterexample

/-!
# `li-projection` · Prescribe: prescribed prices, split three ways (T3)

Package `Cleanroom.Li.LiProjection` ([[li-projection-mandate]]), file 8 of the layout. The
dose-response note's Lemma 4.3 ("prescribed finite prefixes") says: for a day `N*` and a computable
assignment of `[0,1]` prices to sentences on days `< N*`, there is a logical inductor with exactly
those prices on days `< N*`; its *proof* overwrites an inductor's days `< N*` and cites closure under
finite perturbations [LI 4.6.1]. FAF refutes [LI 4.6.1] as printed (`not_overgeneral_ifp`: one
changed day is an infinite computable change carrying unbounded advice) and proves the
finite-*support* form (`lic_iff_of_finiteSupport`). So the claim splits three ways:

* **(a) finite-support prescription** — `prescribe_finiteSupport`: any finitely many
  `(day, sentence)` coordinates can be set to any rationals in `[0,1]` and the result is an
  inductor, with the `ComputableMarket` obligation discharged (`computableMarket_patch`) and the
  prescription exact on the set (`patch_mem`). This is what "steering on finitely many pairs" means.
* **(b) whole-day prescription, the closure form** — `prescribe_wholeDay_closure_false`: the
  statement Lemma 4.3's proof *uses* ("overwrite any inductor's days `< N*` by any computable table
  and the result is still an inductor") is **false**, as a one-line corollary of FAF's
  `not_overgeneral_ifp`. This does *not* refute Lemma 4.3's *statement* (the existence form): the
  counterexample's advice is about the unperturbed market's tail, and another inductor with the
  same prefix is not shown exploitable.
* **(c) the existence form** — OPEN (`prescribe_prefix_exists`, `Open.lean`).
-/

namespace Cleanroom.Li.LiProjection

open LogicalInduction LO.Propositional

attribute [local irreducible] Nat.sqrt

/-! ## The computable market of a finite patch -/

/-- The finite patch table on codes: the entries `(day, ⌜φ⌝, t day φ)` for `(day, φ) ∈ S`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def patchEntries (S : Finset (ℕ × Sentence)) (t : ℕ → Sentence → ℚ) :
    List (ℕ × ℕ × ℚ) :=
  S.toList.map fun p => (p.1, Encodable.encode p.2, t p.1 p.2)

/-- Lookup in a code table by a right fold, falling back to a default.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def tableLookup (l : List (ℕ × ℕ × ℚ)) (n c : ℕ) (d : ℚ) : ℚ :=
  l.foldr (fun x acc => if x.1 = n then (if x.2.1 = c then x.2.2 else acc) else acc) d

/-- `tableLookup_of_forall_ne`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tableLookup_of_forall_ne (l : List (ℕ × ℕ × ℚ)) (n c : ℕ) (d : ℚ)
    (h : ∀ x ∈ l, ¬ (x.1 = n ∧ x.2.1 = c)) : tableLookup l n c d = d := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      simp only [tableLookup, List.foldr_cons]
      have hx := h x (List.mem_cons_self ..)
      have ih' := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
      simp only [tableLookup] at ih'
      by_cases h1 : x.1 = n
      · rw [if_pos h1, if_neg (fun h2 => hx ⟨h1, h2⟩), ih']
      · rw [if_neg h1, ih']

/-- `tableLookup_of_mem`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tableLookup_of_mem (l : List (ℕ × ℕ × ℚ)) (n c : ℕ) (d v : ℚ)
    (hall : ∀ x ∈ l, x.1 = n → x.2.1 = c → x.2.2 = v) (hmem : ∃ x ∈ l, x.1 = n ∧ x.2.1 = c) :
    tableLookup l n c d = v := by
  induction l with
  | nil => obtain ⟨x, hx, -⟩ := hmem; exact absurd hx (List.not_mem_nil)
  | cons x l ih =>
      simp only [tableLookup, List.foldr_cons]
      by_cases h1 : x.1 = n
      · rw [if_pos h1]
        by_cases h2 : x.2.1 = c
        · rw [if_pos h2]
          exact hall x (List.mem_cons_self ..) h1 h2
        · rw [if_neg h2]
          have := ih (fun y hy => hall y (List.mem_cons_of_mem _ hy)) (by
            obtain ⟨y, hy, hy1, hy2⟩ := hmem
            rcases List.mem_cons.mp hy with rfl | hy
            · exact absurd hy2 h2
            · exact ⟨y, hy, hy1, hy2⟩)
          simpa [tableLookup] using this
      · rw [if_neg h1]
        have := ih (fun y hy => hall y (List.mem_cons_of_mem _ hy)) (by
          obtain ⟨y, hy, hy1, hy2⟩ := hmem
          rcases List.mem_cons.mp hy with rfl | hy
          · exact absurd hy1 h1
          · exact ⟨y, hy, hy1, hy2⟩)
        simpa [tableLookup] using this

/-- `tableLookup_prim`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tableLookup_prim (l : List (ℕ × ℕ × ℚ)) :
    Primrec fun z : ℕ × ℕ × ℚ => tableLookup l z.1 z.2.1 z.2.2 := by
  unfold tableLookup
  have hl : Primrec fun _ : ℕ × ℕ × ℚ => l := Primrec.const l
  have hd : Primrec fun z : ℕ × ℕ × ℚ => z.2.2 := Primrec.snd.comp Primrec.snd
  have hstep : Primrec₂ fun (z : ℕ × ℕ × ℚ) (p : (ℕ × ℕ × ℚ) × ℚ) =>
      if p.1.1 = z.1 then (if p.1.2.1 = z.2.1 then p.1.2.2 else p.2) else p.2 := by
    have hx1 : Primrec fun y : (ℕ × ℕ × ℚ) × ((ℕ × ℕ × ℚ) × ℚ) => y.2.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
    have hz1 : Primrec fun y : (ℕ × ℕ × ℚ) × ((ℕ × ℕ × ℚ) × ℚ) => y.1.1 :=
      Primrec.fst.comp Primrec.fst
    have hx2 : Primrec fun y : (ℕ × ℕ × ℚ) × ((ℕ × ℕ × ℚ) × ℚ) => y.2.1.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
    have hz2 : Primrec fun y : (ℕ × ℕ × ℚ) × ((ℕ × ℕ × ℚ) × ℚ) => y.1.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hv : Primrec fun y : (ℕ × ℕ × ℚ) × ((ℕ × ℕ × ℚ) × ℚ) => y.2.1.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
    have hacc : Primrec fun y : (ℕ × ℕ × ℚ) × ((ℕ × ℕ × ℚ) × ℚ) => y.2.2 :=
      Primrec.snd.comp Primrec.snd
    exact Primrec.ite (PrimrecRel.comp Primrec.eq hx1 hz1)
      (Primrec.ite (PrimrecRel.comp Primrec.eq hx2 hz2) hv hacc) hacc
  exact Primrec.list_foldr hl hd hstep

/-- **The patched market is a `ComputableMarket`**: its table is the base table with the finite
code table `patchEntries S t` overriding it.
Source: mandate T3.1 ("with the `ComputableMarket (patch P S t)` obligation discharged")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem computableMarket_patch (P : History) (S : Finset (ℕ × Sentence)) (t : ℕ → Sentence → ℚ)
    (hP : ComputableMarket P) (ht : ∀ p ∈ S, 0 ≤ t p.1 p.2 ∧ t p.1 p.2 ≤ 1) :
    ComputableMarket (patch P S t) := by
  obtain ⟨M⟩ := hP.nonemptyComputation
  refine ComputableMarket.ofComputableTable
    (fun n c => tableLookup (patchEntries S t) n c (M.quote n c)) ?_ ?_ ?_
  · intro n φ
    by_cases h : (n, φ) ∈ S
    · rw [patch_mem P S t h]
      obtain ⟨h0, h1⟩ := ht (n, φ) h
      exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩
    · rw [patch_notMem P S t h]
      exact M.price_mem_Icc n φ
  · intro n φ
    by_cases h : (n, φ) ∈ S
    · rw [patch_mem P S t h]
      congr 1
      symm
      apply tableLookup_of_mem
      · intro x hx h1 h2
        simp only [patchEntries, List.mem_map, Finset.mem_toList] at hx
        obtain ⟨p, -, rfl⟩ := hx
        simp only at h1 h2 ⊢
        have := Encodable.encode_injective h2
        rw [h1, this]
      · exact ⟨(n, Encodable.encode φ, t n φ), by
          simp only [patchEntries, List.mem_map, Finset.mem_toList]
          exact ⟨(n, φ), h, rfl⟩, rfl, rfl⟩
    · rw [patch_notMem P S t h, M.quote_exact n φ]
      congr 1
      symm
      apply tableLookup_of_forall_ne
      intro x hx hc
      simp only [patchEntries, List.mem_map, Finset.mem_toList] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      simp only at hc
      obtain ⟨h1, h2⟩ := hc
      have h2' := Encodable.encode_injective h2
      exact h (by rw [← h1, ← h2']; exact hp)
  · apply Computable.encode.comp
    have hfst : Computable fun z : ℕ => z.unpair.1 := (Primrec.fst.comp Primrec.unpair).to_comp
    have hsnd : Computable fun z : ℕ => z.unpair.2 := (Primrec.snd.comp Primrec.unpair).to_comp
    have hM : Computable fun z : ℕ => M.quote z.unpair.1 z.unpair.2 := by
      have hin : Computable fun z : ℕ => Nat.pair z.unpair.1 z.unpair.2 :=
        Primrec₂.natPair.to_comp.comp hfst hsnd
      have heval : Partrec fun z : ℕ => M.code.eval (Nat.pair z.unpair.1 z.unpair.2) :=
        Nat.Partrec.Code.eval_part.comp (Computable.const M.code) hin
      have henc : Computable fun z : ℕ => Encodable.encode (M.quote z.unpair.1 z.unpair.2) :=
        heval.of_eq fun z => Part.eq_some_iff.mpr (by
          simpa using M.code_spec (Nat.pair z.unpair.1 z.unpair.2))
      exact Computable.encode_iff.mp henc
    have hpair : Computable fun z : ℕ =>
        ((z.unpair.1, (z.unpair.2, M.quote z.unpair.1 z.unpair.2)) : ℕ × ℕ × ℚ) :=
      Computable.pair hfst (Computable.pair hsnd hM)
    have hcomp := (tableLookup_prim (patchEntries S t)).to_comp.comp hpair
    exact hcomp

/-! ## T3.1 (a) Finite-support prescription -/

/-- **Finite-support prescription.** For an inductor `P` over `DP`, a finite coordinate set `S`
and a table `t` with values in `[0,1]` on `S`, the patched market `patch P S t` is a logical
inductor over `DP`; its prices on `S` are exactly `t` (`patch_mem`) and its `ComputableMarket`
obligation is discharged (`computableMarket_patch`). This is the honest finite-support reading
of Lemma 4.3 — "steering on finitely many `(day, sentence)` pairs" — through FAF's corrected
closure theorem `lic_iff_of_finiteSupport`.
Source: [[dose-response]] §4 Lemma 4.3 (finite-support reading); [[anson-inventory]] 051; FAF `thm:ifp` corrected
Kind: C
Fidelity: variant: finite support (finitely many `(day, sentence)` coordinates), not a whole-day prefix — the prefix form is refuted (`prescribe_wholeDay_closure_false`) and the existence form is open (`prescribe_prefix_exists`)
Hyps: (a) -/
theorem prescribe_finiteSupport (P : History) (DP : DeductiveProcess) [hLI : IsLogicalInductor P DP]
    (S : Finset (ℕ × Sentence)) (t : ℕ → Sentence → ℚ)
    (ht : ∀ p ∈ S, 0 ≤ t p.1 p.2 ∧ t p.1 p.2 ≤ 1) :
    IsLogicalInductor (patch P S t) DP :=
  (FreezeOracle.lic_iff_of_finiteSupport P (patch P S t) DP hLI.marketComputable
    (computableMarket_patch P S t hLI.marketComputable ht)
    ⟨S, fun d φ h => (patch_notMem P S t h).symm⟩).mp hLI

/-! ## T3.2 (b) Whole-day prescription: the closure form is false -/

/-- **The whole-day closure claim is false.** It is *not* the case that overwriting any inductor's
prices on days `< N` by any table whose overwrite is a computable market always yields an
inductor (the quantifier is over all tables `t`, with computability carried by the
`ComputableMarket (overwriteBefore P N t)` premise; interchangeable with "any computable table"
here, since the prefix of the overwritten market *is* the table, but that equivalence is not
separately proved): this is the statement Lemma 4.3's proof uses ("overwrite days `< N*` … hence an
inductor by Closure under Finite Perturbations [LI 4.6.1]"), and it is the negation of FAF's
`not_overgeneral_ifp` at the paper's own quantifier (one changed day, an advice-carrying
computable row, the result exploitable). **Not claimed**: that Lemma 4.3's *statement* (the
existence of some inductor with the prescribed prefix) is false — that remains open
(`prescribe_prefix_exists`).
Source: [[dose-response]] §4 Lemma 4.3, proof and the display "any finite pattern of early opinions is criterion-compliant"; FAF `FinitePerturbationCounterexample.not_overgeneral_ifp`
Kind: P
Fidelity: exact (the refuted reading is the proof's closure step; ATTRIBUTION-UNVETTED that the note's display intends the closure reading — findings F2)
Hyps: (a) -/
theorem prescribe_wholeDay_closure_false :
    ¬ ∀ (P : History) (DP : DeductiveProcess) (N : ℕ) (t : ℕ → Sentence → ℚ),
        IsLogicalInductor P DP → ComputableMarket (overwriteBefore P N t) →
        IsLogicalInductor (overwriteBefore P N t) DP := by
  intro H
  apply FinitePerturbationCounterexample.not_overgeneral_ifp
  intro P P' DP N hP hP' htail
  obtain ⟨-, quote, -, hexact, -⟩ := id hP'
  have hEq : overwriteBefore P N (fun n φ => quote n (Encodable.encode φ)) = P' := by
    funext n φ
    unfold overwriteBefore
    by_cases hn : n < N
    · rw [if_pos hn, hexact n φ]
    · rw [if_neg hn, htail n (not_lt.mp hn) φ]
  have := H P DP N (fun n φ => quote n (Encodable.encode φ)) hP (by rw [hEq]; exact hP')
  rwa [hEq] at this

/-- The overwrite is exact on the prefix.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma overwriteBefore_lt (P : History) (N : ℕ) (t : ℕ → Sentence → ℚ) {n : ℕ} (h : n < N)
    (φ : Sentence) : overwriteBefore P N t n φ = (t n φ : ℝ) := by
  simp [overwriteBefore, h]

end Cleanroom.Li.LiProjection
