import Cleanroom.Bli.BliFinite.WorldRound
import Cleanroom.Bli.BliFinite.Superbelief
import LogicalInduction.Framework.Criterion

/-!
# `bli-superbelief` · CoherentGrid: coherent grids force a coherent base (E7, finite part)

If every point charged by a balance solution is propositionally coherent (`bli-finite`'s
`CoherentOn`: the marginal of a rational probability on `FiniteWorld B` supported on
`D`-consistent worlds), then the base table is coherent with the same `D`, `B`: **mix the world
measures** with the solution's weights (`base_coherent_of_coherentGrid`). Over the coherent grid
every point is coherent (`coherentOn_of_mem_coherentGrid`), so *any* balance solution on it forces
the base coherent (`base_coherent_of_balance_on_coherentGrid`) — Appendix B's opening assumption
is forced by its grid. Contrapositive: an incoherent base has **no** balance solution on the
coherent grid (`faceGen_coherentGrid_eq_empty_of_not_coherent`). A base pricing both `φ` and
`∼φ` at `0` is incoherent for every `D`, `B` (`not_coherent_of_offSupport_pair`: a world marginal
has `t φ + t (∼φ) = 1`). The FAF instance (both off the LIA's support) is `Paper.lean`'s.

No atom bound `hB` is needed here: `CoherentOn` is the world-marginal form, and the restriction
to day `m` only reads the day-`m` coordinates of the mixed marginal. (`hB` enters only when the
two-axiom form is wanted, `coherentOn_iff_twoAxiom`.) Only `bli-finite`'s finite `CoherentOn` is
used — never a limit notion.

Sources: [[bli-program]] §3.5(ii) (`C:E5`, new), §3.10 row E7, §8 item 3; bli-slides-017's flag
(summing over incoherent grid points); bli-soto-a-034.
-/

namespace Cleanroom.Bli.BliSuperbelief

open LogicalInduction LO.Propositional Finset BoolPCWorld Cleanroom.Bli.BliFinite

variable {𝒮 : SmallIndex} {m : ℕ}

/-! ## Mixing world measures -/

/-- Coherence of a day-`(m+1)` table restricts to day `m` (the same world measure).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma coherentOn_restrict {Q : Table 𝒮 (m + 1)} {D : Finset Sentence} {B : ℕ}
    (h : CoherentOn Q D B) : CoherentOn Q.restrict D B := by
  obtain ⟨w, hw0, hw1, hD, hQ⟩ := h
  exact ⟨w, hw0, hw1, hD, fun φ => hQ ⟨φ.1, 𝒮.mono m φ.2⟩⟩

/-- **E7(a), coherent grids force a coherent base.** If `F` is a probability on `G` with restricted
mean `t` and every point of `G` that `F` charges is `CoherentOn · D B` **on `S m`** (its
restriction is coherent — the program's "every grid table is coherent on `S_{n−1}`"; coherence on
all of `S (m+1)` implies it, `coherentOn_restrict`), then `t` is `CoherentOn · D B`: the world
measure `w := ∑_Q F Q · w_Q` (one chosen world measure per charged point) is a probability on
`D`-consistent worlds whose marginal on the day-`m` sentences is `t`.
Source: [[bli-program]] §3.5(ii) (`C:E5`; "mix the world measures"; "every grid table is coherent
on `S_{n−1}`"); audit r1 (fidelity §3.2)
Kind: P
Fidelity: exact (the hypothesis is the program's, on `S m`)
Hyps: (a) none beyond `IsProbOn`, balance and coherence of the charged points on `S m` -/
theorem base_coherent_of_coherentGrid {G : Finset (Table 𝒮 (m + 1))} {F : Superbelief 𝒮 (m + 1)}
    {t : Table 𝒮 m} (hF : IsProbOn G F) (hb : (meanOn G F).restrict = t) {D : Finset Sentence}
    {B : ℕ} (hcoh : ∀ Q ∈ G, 0 < F Q → CoherentOn Q.restrict D B) : CoherentOn t D B := by
  classical
  -- one chosen world measure per charged point, zero elsewhere
  let wQ : Table 𝒮 (m + 1) → FiniteWorld B → ℚ := fun Q =>
    if h : Q ∈ G ∧ 0 < F Q then Classical.choose (hcoh Q h.1 h.2) else 0
  have hwQ : ∀ Q (h : Q ∈ G ∧ 0 < F Q),
      (∀ u, 0 ≤ wQ Q u) ∧ ∑ u, wQ Q u = 1 ∧
      (∀ u, wQ Q u ≠ 0 → (worldOf u).ConsistentWith D) ∧
      ∀ φ : ↥(𝒮.S m), Q.restrict φ = ∑ u, wQ Q u * u.payoutRat φ.1 := by
    intro Q h
    simp only [wQ, dif_pos h]
    exact Classical.choose_spec (hcoh Q h.1 h.2)
  have hzero : ∀ Q, ¬ (0 < F Q) → F Q = 0 := fun Q h => le_antisymm (not_lt.mp h) (hF.1 Q)
  refine ⟨fun u => ∑ Q ∈ G, F Q * wQ Q u, ?_, ?_, ?_, ?_⟩
  · -- nonnegative
    intro u
    apply Finset.sum_nonneg
    intro Q hQ
    apply mul_nonneg (hF.1 Q)
    by_cases h : 0 < F Q
    · exact (hwQ Q ⟨hQ, h⟩).1 u
    · simp only [wQ, dif_neg (fun h' : Q ∈ G ∧ 0 < F Q => h h'.2)]
      exact le_rfl
  · -- total mass one
    rw [Finset.sum_comm]
    calc ∑ Q ∈ G, ∑ u, F Q * wQ Q u = ∑ Q ∈ G, F Q := by
          apply Finset.sum_congr rfl
          intro Q hQ
          rw [← Finset.mul_sum]
          by_cases h : 0 < F Q
          · rw [(hwQ Q ⟨hQ, h⟩).2.1, mul_one]
          · rw [hzero Q h, zero_mul]
      _ = 1 := hF.2.2
  · -- supported on `D`-consistent worlds
    intro u hu
    obtain ⟨Q, hQ, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
    have hFQ : 0 < F Q := by
      by_contra h
      exact hne (by rw [hzero Q h, zero_mul])
    have hw : wQ Q u ≠ 0 := fun h => hne (by rw [h, mul_zero])
    exact (hwQ Q ⟨hQ, hFQ⟩).2.2.1 u hw
  · -- the marginal is `t`
    intro φ
    have hb' := congrFun hb φ
    rw [Table.restrict_apply] at hb'
    rw [← hb']
    unfold meanOn
    calc ∑ Q ∈ G, F Q * Q ⟨φ.1, 𝒮.mono m φ.2⟩
        = ∑ Q ∈ G, F Q * ∑ u, wQ Q u * u.payoutRat φ.1 := by
          apply Finset.sum_congr rfl
          intro Q hQ
          by_cases h : 0 < F Q
          · rw [show Q ⟨φ.1, 𝒮.mono m φ.2⟩ = Q.restrict φ from rfl, (hwQ Q ⟨hQ, h⟩).2.2.2 φ]
          · rw [hzero Q h, zero_mul, zero_mul]
      _ = ∑ u, (∑ Q ∈ G, F Q * wQ Q u) * u.payoutRat φ.1 := by
          simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
          rw [Finset.sum_comm]

/-- **E7(a), over the coherent grid.** Any balance solution on the coherent grid
`coherentGrid 𝒮 d (m+1) D B` (`0 < d (m+1)`) forces the base table `CoherentOn · D B`:
"Appendix B's opening assumption is forced by its grid".
Source: [[bli-program]] §3.5(ii) (`C:E5`)
Kind: C
Fidelity: exact
Hyps: (a) `0 < d (m+1)` -/
theorem base_coherent_of_balance_on_coherentGrid {d : ℕ → ℕ} (hd : 0 < d (m + 1))
    {D : Finset Sentence} {B : ℕ} {F : Superbelief 𝒮 (m + 1)} {t : Table 𝒮 m}
    (hF : IsProbOn (coherentGrid 𝒮 d (m + 1) D B) F)
    (hb : (meanOn (coherentGrid 𝒮 d (m + 1) D B) F).restrict = t) : CoherentOn t D B :=
  base_coherent_of_coherentGrid hF hb fun _ hQ _ =>
    coherentOn_restrict (coherentOn_of_mem_coherentGrid hd hQ)

/-- **Contrapositive: an incoherent base has no balance solution on the coherent grid** — the
generated face over it is empty, so E1's existence theorem is vacuous there and B1 must use the
product grid (the program's resolution).
Source: [[bli-program]] §3.5(ii) ("the coherent grid is infeasible on every such day")
Kind: C
Fidelity: exact
Hyps: (a) `0 < d (m+1)`; (a) `¬ CoherentOn t D B` -/
theorem faceGen_coherentGrid_eq_empty_of_not_coherent {d : ℕ → ℕ} (hd : 0 < d (m + 1))
    {D : Finset Sentence} {B : ℕ} {t : Table 𝒮 m} (hnc : ¬ CoherentOn t D B) :
    faceGen (coherentGrid 𝒮 d (m + 1) D B) t = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro Q hQ
  obtain ⟨-, F, hF, hb, -⟩ := mem_faceGen_iff.mp hQ
  exact hnc (base_coherent_of_balance_on_coherentGrid hd hF hb)

/-! ## An off-support pair is incoherent -/

/-- A world pays `1` on exactly one of `φ`, `∼φ`.
Source: none: infrastructure (FAF `PCWorld.holds_neg`)
Kind: L
Fidelity: n/a -/
lemma payoutRat_add_neg {B : ℕ} (u : FiniteWorld B) (φ : Sentence) :
    u.payoutRat φ + u.payoutRat (∼φ) = 1 := by
  rw [payoutRat_eq_ite, payoutRat_eq_ite, PCWorld.holds_neg]
  by_cases h : (worldOf u).Holds φ <;> simp [h]

/-- A coherent table prices `φ` and `∼φ` (both small) to `1` in total.
Source: none: infrastructure (FAF `PCWorld.holds_neg`)
Kind: L
Fidelity: n/a -/
lemma coherentOn_add_neg {t : Table 𝒮 m} {φ : Sentence} (hφ : φ ∈ 𝒮.S m) (hnφ : ∼φ ∈ 𝒮.S m)
    {D : Finset Sentence} {B : ℕ} (h : CoherentOn t D B) : t ⟨φ, hφ⟩ + t ⟨∼φ, hnφ⟩ = 1 := by
  obtain ⟨w, hw0, hw1, -, ht⟩ := h
  rw [ht, ht, ← Finset.sum_add_distrib]
  calc ∑ u, (w u * u.payoutRat φ + w u * u.payoutRat (∼φ)) = ∑ u, w u := by
        apply Finset.sum_congr rfl
        intro u _
        rw [← mul_add, payoutRat_add_neg, mul_one]
    _ = 1 := hw1

/-- **E7(b), one-sided form.** A table pricing a small `φ` at exactly `0` whose small negation is
not priced exactly `1` is not `CoherentOn · D B` for any `D`, `B`: a world marginal has
`t φ + t (∼φ) = 1`. This is the program's "every day with an off-support `φ`" — the negation off
the support (priced `0`) is the special case `not_coherent_of_offSupport_pair`.
Source: [[bli-program]] §3.5(ii) ("every day with an off-support `φ`"); bli-soto-a-034; audit r1
(fidelity §3.3)
Kind: P
Fidelity: stronger: one off-support sentence with `t (∼φ) ≠ 1` suffices
Hyps: (a) none -/
theorem not_coherent_of_zero_of_neg_ne_one {t : Table 𝒮 m} {φ : Sentence} (hφ : φ ∈ 𝒮.S m)
    (hnφ : ∼φ ∈ 𝒮.S m) (h0 : t ⟨φ, hφ⟩ = 0) (h1 : t ⟨∼φ, hnφ⟩ ≠ 1) (D : Finset Sentence) (B : ℕ) :
    ¬ CoherentOn t D B := by
  intro h
  have hsum := coherentOn_add_neg hφ hnφ h
  rw [h0, zero_add] at hsum
  exact h1 hsum

/-- **E7(b), the pair form.** A table pricing both `φ` and `∼φ` (both small on day `m`) at exactly
`0` is not `CoherentOn · D B` for any `D`, `B` — the special case `t (∼φ) = 0 ≠ 1` of
`not_coherent_of_zero_of_neg_ne_one`.
Source: [[bli-program]] §3.5(ii) ("every day with an off-support `φ`: both `φ` and `¬φ` quote 0");
bli-soto-a-034
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem not_coherent_of_offSupport_pair {t : Table 𝒮 m} {φ : Sentence} (hφ : φ ∈ 𝒮.S m)
    (hnφ : ∼φ ∈ 𝒮.S m) (h0 : t ⟨φ, hφ⟩ = 0) (h0' : t ⟨∼φ, hnφ⟩ = 0) (D : Finset Sentence) (B : ℕ) :
    ¬ CoherentOn t D B :=
  not_coherent_of_zero_of_neg_ne_one hφ hnφ h0 (by rw [h0']; norm_num) D B

end Cleanroom.Bli.BliSuperbelief
