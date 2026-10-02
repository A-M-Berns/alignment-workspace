import Cleanroom.Bli.BliTrajectory.Lemmas

/-!
# `bli-trajectory` · Degenerate: B0, the degenerate solution (M2, E4)

Appendix B's "unsatisfying" solution (`main.tex:447–449`): `𝐏_{n-1}(𝐐_n = Q) = 1` when `Q`
describes the current beliefs, `0` otherwise. Finite objects first (`pointMass`, `extendZero`,
`degStep`, `degLaw`): the point-mass law is balanced at `t` **iff** `t` is already on the next
day's grid values (`degLaw_balanced_iff`), so it is **not a `Kernel`** whenever the day has a
sentence (`degLaw_not_kernel`), and it is never non-degenerate at an interior table
(`pointMass_not_nonDegenerate`). Then B0's history `b0History` (built directly in `Defs.lean`
from the deterministic continuation `degAt`): `E1x`, the scoped `E2x`/`E3`, `E5` hold outright,
`E4` holds on the denominator grid, and the realized next state has positive mass **iff** the
rounded prices did not move (`b0_pos_iff`). Ledger grade `N−`: B0 is the degenerate witness the
sources exhibit; the tent instance (`Lemmas.lean`) is the `N+`.
-/

namespace Cleanroom.Bli.BliTrajectory

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite

open Classical

/-! ## The finite objects -/

section Finite

variable {𝒮 : SmallIndex} {m : ℕ}

/-- `pointMass` unfolded.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pointMass_apply (t Q : Table 𝒮 m) : pointMass t Q = if Q = t then 1 else 0 := rfl

/-- A point mass at a point of `G` is a probability on `G`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pointMass_isProbOn {G : Finset (Table 𝒮 m)} {t : Table 𝒮 m} (ht : t ∈ G) :
    IsProbOn G (pointMass t) := by
  refine ⟨fun Q => ?_, fun Q hQ => ?_, ?_⟩
  · rw [pointMass_apply]; split_ifs <;> norm_num
  · rw [pointMass_apply, if_neg]; rintro rfl; exact hQ ht
  · simp only [pointMass_apply]
    rw [Finset.sum_ite_eq' G t]; rw [if_pos ht]

/-- The mean of a point mass is its point.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma meanOn_pointMass {G : Finset (Table 𝒮 m)} {t : Table 𝒮 m} (ht : t ∈ G) :
    meanOn G (pointMass t) = t := by
  funext φ
  unfold meanOn
  simp only [pointMass_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' G t, if_pos ht]

/-- Restricting an extension by zero gives the table back.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma extendZero_restrict (t : Table 𝒮 m) : (extendZero t).restrict = t := by
  funext φ
  rw [Table.restrict_apply]
  unfold extendZero
  rw [dif_pos φ.2]

/-- The extension by zero on an old coordinate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma extendZero_old (t : Table 𝒮 m) (φ : ↥(𝒮.S (m + 1))) (h : φ.1 ∈ 𝒮.S m) :
    extendZero t φ = t ⟨φ.1, h⟩ := by
  unfold extendZero; rw [dif_pos h]

/-- The extension by zero on a new coordinate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma extendZero_new (t : Table 𝒮 m) (φ : ↥(𝒮.S (m + 1))) (h : φ.1 ∉ 𝒮.S m) :
    extendZero t φ = 0 := by
  unfold extendZero; rw [dif_neg h]

/-- An extension by zero of a table with next-day grid values is a next-day grid table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma extendZero_mem_grid {d : ℕ → ℕ} {t : Table 𝒮 m} (ht : ∀ φ, t φ ∈ gridVals (d (m + 1))) :
    extendZero t ∈ grid 𝒮 d (m + 1) := by
  rw [mem_grid_iff]
  intro φ
  unfold extendZero
  split_ifs with h
  · exact ht _
  · exact zero_mem_gridVals _

/-- The degenerate step lands on the next day's grid (unconditionally, by the clamp).
Source: mandate D3
Kind: L
Fidelity: n/a -/
lemma degStep_mem_grid (d : ℕ → ℕ) (t : Table 𝒮 m) : degStep d m t ∈ grid 𝒮 d (m + 1) :=
  extendZero_mem_grid (fun _ => roundVal_mem_gridVals _ _)

/-- The degenerate step on an old coordinate is the rounded price.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma degStep_old (d : ℕ → ℕ) (t : Table 𝒮 m) (φ : ↥(𝒮.S m)) :
    degStep d m t ⟨φ.1, 𝒮.mono m φ.2⟩ = roundVal (d (m + 1)) (t φ) := by
  unfold degStep
  rw [extendZero_old _ _ φ.2]
  rfl

/-- **The point-mass law is balanced at `t` iff `t` is already on the next day's grid values.**
(Restricted to the old coordinates; the mandate's `↔ t ∈ grid … m` is the special case
`d (m+1) = d m`, since `gridVals (d m) ⊆ gridVals (d (m+1))`.) So B0's law is balanced only on
the denominator grid — Appendix B's degenerate solution presupposes exact rounding.
Source: Appendix B (`main.tex:447`); bli-soto-a-006 (ii) (B0 needs nested grids); mandate M2
Kind: P
Fidelity: variant: next-day grid values in place of the mandate's day-`m` grid (the true condition)
Hyps: (a) none -/
theorem degLaw_balanced_iff (d : ℕ → ℕ) (hd : 0 < d (m + 1)) (t : Table 𝒮 m) :
    BliFinite.Balanced d (degLaw d m t) t ↔ ∀ φ, t φ ∈ gridVals (d (m + 1)) := by
  unfold BliFinite.Balanced degLaw
  have hmean : mean d (pointMass (degStep d m t)) = degStep d m t :=
    meanOn_pointMass (degStep_mem_grid d t)
  rw [hmean]
  constructor
  · intro h φ
    have := h φ
    rw [Table.restrict_apply, degStep_old] at this
    rw [← this]; exact roundVal_mem_gridVals _ _
  · intro h φ
    rw [Table.restrict_apply, degStep_old]
    exact roundVal_eq_self hd (h φ)

/-- A day-`m` grid table is balanced under the point-mass law (nested grids).
Source: bli-soto-a-006 (ii); mandate M2
Kind: L
Fidelity: exact -/
lemma degLaw_balanced_of_mem_grid (𝓜 : Mesh) {t : Table 𝒮 m} (ht : t ∈ grid 𝒮 𝓜.d m) :
    BliFinite.Balanced 𝓜.d (degLaw 𝓜.d m t) t :=
  (degLaw_balanced_iff 𝓜.d (𝓜.d_pos _) t).mpr
    (fun φ => gridVals_mono (𝓜.d_dvd m) (𝓜.d_pos _) (mem_grid_iff.mp ht φ))

/-- **The degenerate law is not a `Kernel`** once the day has a sentence: the unit-cube table
`1 / (2 d_{m+1})` is off the next day's grid values, so no kernel (balanced on the whole cube)
has it as its law. No tent fallback is smuggled in: B0 is built directly (`b0History`).
Source: mandate D3 ("not a `Kernel` in general")
Kind: P
Fidelity: exact
Hyps: (a) `hS`: the day has a small sentence -/
theorem degLaw_not_kernel (𝓜 : Mesh) (hS : (𝒮.S m).Nonempty) :
    ¬ ∃ κ : Kernel 𝒮 𝓜.d m, ∀ t, κ.law t = degLaw 𝓜.d m t := by
  rintro ⟨κ, hκ⟩
  have hd := 𝓜.d_pos (m + 1)
  have hdq : (0 : ℚ) < 𝓜.d (m + 1) := by exact_mod_cast hd
  set t : Table 𝒮 m := fun _ => 1 / (2 * 𝓜.d (m + 1)) with ht
  have htu : t.InUnit := by
    intro φ
    simp only [ht]
    constructor
    · positivity
    · rw [div_le_one (by positivity)]
      have : (1 : ℚ) ≤ 𝓜.d (m + 1) := by exact_mod_cast hd
      linarith
  have hbal := κ.balanced t htu
  rw [hκ, degLaw_balanced_iff 𝓜.d hd] at hbal
  obtain ⟨φ, hφ⟩ := hS
  obtain ⟨k, -, hk⟩ := mem_gridVals_iff.mp (hbal ⟨φ, hφ⟩)
  simp only [ht] at hk
  field_simp at hk
  have : (2 * k : ℚ) = 1 := by linarith
  have h2 : (2 * k : ℕ) = 1 := by exact_mod_cast this
  omega

/-- **A point mass is never non-degenerate at an interior table**: if `t` prices some sentence
strictly inside `(0,1)`, the product face has two distinct points (sending that sentence to `0`
and to `1`), and a point mass charges at most one.
Source: bli-slides-018/021 (non-degeneracy); Appendix B (`main.tex:447–449`); mandate M2
Kind: P
Fidelity: exact (no `d ≥ 2` needed: `0` and `1` are grid values)
Hyps: (a) `0 < d (m+1)`; (a) an interior coordinate -/
theorem pointMass_not_nonDegenerate (d : ℕ → ℕ) (hd : 0 < d (m + 1)) (p : Table 𝒮 (m + 1))
    {t : Table 𝒮 m} {φ : ↥(𝒮.S m)} (h0 : 0 < t φ) (h1 : t φ < 1) :
    ¬ NonDegenerate d (pointMass p) t := by
  intro hnd
  let mk : ℚ → Table 𝒮 (m + 1) := fun v ψ =>
    if ψ.1 = φ.1 then v else if h : ψ.1 ∈ 𝒮.S m then (if t ⟨ψ.1, h⟩ = 1 then 1 else 0) else 0
  have hface : ∀ v, v ∈ gridVals (d (m + 1)) → mk v ∈ faceProd 𝒮 d m t := by
    intro v hv
    rw [mem_faceProd_iff]
    constructor
    · rw [mem_grid_iff]
      intro ψ
      show (if ψ.1 = φ.1 then v else if h : ψ.1 ∈ 𝒮.S m then (if t ⟨ψ.1, h⟩ = 1 then 1 else 0)
        else 0) ∈ _
      split_ifs
      · exact hv
      · exact one_mem_gridVals hd
      · exact zero_mem_gridVals _
      · exact zero_mem_gridVals _
    · intro ψ hψ
      rw [Table.restrict_apply]
      show (if ψ.1 = φ.1 then v else if h : ψ.1 ∈ 𝒮.S m then (if t ⟨ψ.1, h⟩ = 1 then 1 else 0)
        else 0) = t ψ
      have hne : ψ.1 ≠ φ.1 := by
        intro h
        have hψφ : ψ = φ := Subtype.ext h
        rw [hψφ] at hψ
        rcases hψ with h' | h' <;> linarith
      rw [if_neg hne, dif_pos ψ.2]
      rcases hψ with h' | h'
      · rw [if_neg (by rw [h']; exact zero_ne_one), h']
      · rw [if_pos h', h']
  have h0' := hnd (mk 0) (hface 0 (zero_mem_gridVals _))
  have h1' := hnd (mk 1) (hface 1 (one_mem_gridVals hd))
  rw [pointMass_apply] at h0' h1'
  split_ifs at h0' with e0
  · split_ifs at h1' with e1
    · have := congrFun (e0.trans e1.symm) ⟨φ.1, 𝒮.mono m φ.2⟩
      simp [mk] at this
    · exact lt_irrefl _ h1'
  · exact lt_irrefl _ h0'

end Finite

/-! ## The deterministic continuation -/

section Continuation

variable {𝒮 : SmallIndex} (d : ℕ → ℕ) {n : ℕ} (t : Table 𝒮 n)

/-- Transport of the iterated continuation along an equality of horizons.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma degIter_castDay {h h' : ℕ} (e : h = h') (e' : n + h = n + h') :
    (degIter d t h).castDay e' = degIter d t h' := by
  subst e; rfl

/-- The continuation on day `n + h` is the `h`-fold iterate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma degAt_add (h : ℕ) : degAt d t (n + h) = degIter d t h := by
  unfold degAt
  rw [dif_pos (Nat.le_add_right n h)]
  exact degIter_castDay d t (Nat.add_sub_cancel_left n h) _

/-- The continuation on day `n` is the table itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma degAt_self : degAt d t n = t := degAt_add d t 0

/-- The continuation steps by `degStep`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma degAt_succ {j : ℕ} (hj : n ≤ j) : degAt d t (j + 1) = degStep d j (degAt d t j) := by
  obtain ⟨h, rfl⟩ := Nat.exists_eq_add_of_le hj
  show degAt d t (n + (h + 1)) = degStep d (n + h) (degAt d t (n + h))
  rw [degAt_add, degAt_add]
  rfl

/-- The continuation on a later day is a grid table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma degAt_mem_grid {j : ℕ} (hj : n < j) : degAt d t j ∈ grid 𝒮 d j := by
  obtain ⟨h, rfl⟩ := Nat.exists_eq_add_of_lt hj
  show degAt d t (n + (h + 1)) ∈ _
  rw [degAt_add]
  exact degStep_mem_grid d _

end Continuation

/-! ## B0's history -/

variable {𝓜 : Mesh} (c : StateCoding 𝓜) (Q : RatHistory)

/-- The B0 price of a future candidate atom: `1` iff its code is the continuation's code.
Source: Appendix B (`main.tex:447`)
Kind: L
Fidelity: n/a -/
lemma b0Price_stateAtom {n m q : ℕ} (hnm : n < m) (hq : q ∈ c.states m) :
    b0Price Q 𝓜 c n (stateAtom m q) =
      if q = c.code m (degAt 𝓜.d (actualTable smallIndex Q n) m) then 1 else 0 := by
  rw [b0Price_of_tierA (not_smallOn_stateAtom c hnm hq) (tierA_stateAtom c hnm hq)]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true,
    smallFactor_none]

/-- The B0 price of `φ ⋏ σ` is the table value times the price of `σ`.
Source: Appendix B constraint 2 (`main.tex:432`)
Kind: L
Fidelity: n/a -/
lemma b0Price_and_stateAtom {n m q : ℕ} (hnm : n < m) (hq : q ∈ c.states m) {φ : Sentence}
    (hno : NoFutureState c n φ) (hsm : SmallOn m φ) :
    b0Price Q 𝓜 c n (φ ⋏ stateAtom m q) = c.tableVal m q φ * b0Price Q 𝓜 c n (stateAtom m q) := by
  rw [b0Price_of_tierA (not_smallOn_and_of_right (not_smallOn_stateAtom c hnm hq))
      (tierA_and_stateAtom c hnm hq hno hsm), b0Price_stateAtom c Q hnm hq]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true,
    smallFactor_some, latestEntry_singleton]
  split_ifs <;> simp

/-- **`b0_small`**: B0 copies the base on small sentences.
Source: Appendix B constraint 1; mandate M2
Kind: L
Fidelity: exact -/
theorem b0_small : E1x (ratHistory Q) (b0History Q 𝓜 c) := by
  intro n φ hφ
  unfold b0History ratHistory
  rw [b0Price_of_small (mem_smallSet.mp hφ)]

/-- **`b0_cond2_scoped`**: B0 satisfies the scoped constraint 2.
Source: Appendix B constraint 2; mandate M2
Kind: L
Fidelity: weaker: scope restricted as `bli_cond2_scoped` -/
theorem b0_cond2_scoped : E2xScoped c (bliStateSystem Q 𝓜 c) (b0History Q 𝓜 c) := by
  intro n m hnm q hq φ hφ hno
  simp only [bliStateSystem_states] at hq
  have hsm : SmallOn m φ := mem_smallSet.mp (Sminus_subset_smallSet m m hφ)
  unfold b0History
  rw [b0Price_and_stateAtom c Q hnm hq hno hsm, bliStateSystem_val]
  push_cast; ring

/-- **`b0_cond3_scoped`**: B0 satisfies the scoped constraint 3.
Source: Appendix B constraint 3; mandate M2
Kind: L
Fidelity: weaker: scope restricted as `bli_cond3_scoped` -/
theorem b0_cond3_scoped : E3Scoped c (bliStateSystem Q 𝓜 c) (b0History Q 𝓜 c) := by
  intro n m o hnm hmo q₁ hq₁ q₂ hq₂ φ hφ hno
  simp only [bliStateSystem_states] at hq₁ hq₂
  have hno' : n < o := hnm.trans hmo
  have hso : SmallOn o φ := (mem_smallSet.mp (Sminus_subset_smallSet m m hφ)).mono hmo.le
  have hlarge : ¬ SmallOn n (stateAtom m q₁ ⋏ stateAtom o q₂) :=
    not_smallOn_and_of_left (not_smallOn_stateAtom c hnm hq₁)
  unfold b0History
  rw [b0Price_of_tierA (not_smallOn_and_of_right hlarge) (tierA_and_two c hnm hq₁ hno' hq₂ hmo hno hso),
    b0Price_of_tierA hlarge (tierA_stateAtom_and_stateAtom c hnm hq₁ hno' hq₂), bliStateSystem_val]
  simp only [smallFactor_some, smallFactor_none, latestEntry_pair_of_lt hmo]
  split_ifs <;> simp

/-- **`b0_partition`**: B0's superbeliefs sum to one (exactly one candidate, the continuation's
code, has mass) and are exclusive.
Source: bli-slides-017 (5); mandate M2
Kind: L
Fidelity: exact -/
theorem b0_partition : E5 (bliStateSystem Q 𝓜 c) (b0History Q 𝓜 c) := by
  intro n
  have hmem : c.code (n + 1) (degAt 𝓜.d (actualTable smallIndex Q n) (n + 1)) ∈ c.states (n + 1) :=
    c.code_mem_states (degAt_mem_grid 𝓜.d _ (Nat.lt_succ_self n))
  have key : ∀ q ∈ c.states (n + 1), b0History Q 𝓜 c n (stateAtom (n + 1) q) =
      if q = c.code (n + 1) (degAt 𝓜.d (actualTable smallIndex Q n) (n + 1)) then (1 : ℝ) else 0 := by
    intro q hq
    unfold b0History
    rw [b0Price_stateAtom c Q (Nat.lt_succ_self n) hq]
    split_ifs <;> simp
  constructor
  · simp only [bliStateSystem_states]
    rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' (c.states (n + 1)), if_pos hmem]
  · intro q₁ hq₁ q₂ hq₂ hne
    simp only [bliStateSystem_states] at hq₁ hq₂
    unfold b0History
    rw [b0Price_of_tierA (not_smallOn_and_of_left (not_smallOn_stateAtom c (Nat.lt_succ_self n) hq₁))
        (tierA_stateAtom_and_stateAtom c (Nat.lt_succ_self n) hq₁ (Nat.lt_succ_self n) hq₂)]
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    rw [if_neg]
    · simp
    · rintro ⟨h1, h2⟩; exact hne (h1.trans h2.symm)

/-- **`b0_balance` — constraint 4 for B0 on the denominator grid**: when every small price is
already a next-day grid value, `𝐏⁰_n(φ) = Q_n(φ) = ∑_q 𝐏⁰_n(σ_q) Q̂_q[φ]` (the single charged
table is the rounded actual table, and rounding is the identity there). Off the denominator
grid `E4` fails for B0 (`degLaw_balanced_iff`).
Source: Appendix B constraint 4 (`main.tex:434`); bli-soto-a-006 (ii); mandate M2
Kind: L
Fidelity: weaker: needs the denominator-grid hypothesis
Hyps: (a) `hgrid`: every small price is a next-day grid value -/
theorem b0_balance (hgrid : ∀ n φ, φ ∈ smallSet n → Q n φ ∈ gridVals (𝓜.d (n + 1))) :
    E4 (bliStateSystem Q 𝓜 c) (b0History Q 𝓜 c) := by
  intro n φ hφ
  have hφ' : φ ∈ smallSet (n + 1) := smallSet_mono (Nat.le_succ n) hφ
  have hD : degAt 𝓜.d (actualTable smallIndex Q n) (n + 1) ∈ grid smallIndex 𝓜.d (n + 1) :=
    degAt_mem_grid 𝓜.d _ (Nat.lt_succ_self n)
  have hmem := c.code_mem_states hD
  have hL : b0History Q 𝓜 c n φ = (Q n φ : ℝ) := by
    unfold b0History; rw [b0Price_of_small (mem_smallSet.mp hφ)]
  rw [hL]
  simp only [bliStateSystem_states, bliStateSystem_val]
  have key : ∀ q ∈ c.states (n + 1),
      b0History Q 𝓜 c n (stateAtom (n + 1) q) * (c.tableVal (n + 1) q φ : ℝ) =
        if q = c.code (n + 1) (degAt 𝓜.d (actualTable smallIndex Q n) (n + 1))
        then (c.tableVal (n + 1) q φ : ℝ) else 0 := by
    intro q hq
    unfold b0History
    rw [b0Price_stateAtom c Q (Nat.lt_succ_self n) hq]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' (c.states (n + 1)), if_pos hmem,
    c.tableVal_code hD hφ', degAt_succ 𝓜.d _ le_rfl, degAt_self]
  have h2 : degStep 𝓜.d n (actualTable smallIndex Q n) ⟨φ, hφ'⟩ =
      roundVal (𝓜.d (n + 1)) (Q n φ) := degStep_old 𝓜.d _ ⟨φ, hφ⟩
  rw [h2, roundVal_eq_self (𝓜.d_pos _) (hgrid n φ hφ)]

/-- **`b0_isBLI_scoped`**: on the denominator grid, B0 satisfies the scoped Roman bundle — the
degenerate solution passes Appendix B's constraints (as the paper says, `main.tex:447`).
Source: Appendix B (`main.tex:447`); mandate M2
Kind: C
Fidelity: weaker: faith predicates scoped; `E4` on the denominator grid
Hyps: (a) `hgrid` -/
theorem b0_isBLI_scoped (hgrid : ∀ n φ, φ ∈ smallSet n → Q n φ ∈ gridVals (𝓜.d (n + 1))) :
    IsBLI_RomanScoped c (bliStateSystem Q 𝓜 c) (ratHistory Q) (b0History Q 𝓜 c) :=
  ⟨b0_small c Q, b0_cond2_scoped c Q, b0_cond3_scoped c Q, b0_balance c Q hgrid, b0_partition c Q⟩

/-- **B0's realized next state has positive mass iff the rounded prices did not move**: the
realized day-`(n+1)` state is the rounded day-`(n+1)` table, and B0 charges only the day-`n`
table rounded to the day-`(n+1)` grid and extended by zero. (bli-slides-005: "any change in
prices would be an update on a probability zero event".) So `BayesRatio` is available for B0
exactly on those days. The right-hand side `actualState (n+1) = degStep n (actualTable n)` also
requires every *new* day-`(n+1)` small sentence to round to `0` (the `extendZero` convention,
D3): "the rounded prices did not move" includes "the new prices round to zero".
Source: Appendix B (`main.tex:447–449`); bli-slides-005; bli-paper-043 (finite half); mandate M2
Kind: P
Fidelity: exact (rounded to the day-`(n+1)` grid; the mandate's `extendZero (actualState n)`
rounds to the day-`n` grid and coincides on the denominator grid)
Hyps: (a) none -/
theorem b0_pos_iff (n : ℕ) :
    0 < b0History Q 𝓜 c n (stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) ↔
      actualState smallIndex 𝓜.d Q (n + 1) = degStep 𝓜.d n (actualTable smallIndex Q n) := by
  have hA : actualState smallIndex 𝓜.d Q (n + 1) ∈ grid smallIndex 𝓜.d (n + 1) :=
    actualState_mem_grid
  have hD : degStep 𝓜.d n (actualTable smallIndex Q n) ∈ grid smallIndex 𝓜.d (n + 1) :=
    degStep_mem_grid _ _
  simp only [bliStateSystem_actual]
  unfold b0History
  rw [b0Price_stateAtom c Q (Nat.lt_succ_self n) (c.code_mem_states hA),
    degAt_succ 𝓜.d _ le_rfl, degAt_self]
  constructor
  · intro h
    split_ifs at h with e
    · exact c.inj (n + 1) hA hD e
    · simp at h
  · intro e
    rw [if_pos (by rw [e])]
    norm_num

/-- **B0's superbelief is a point mass**: exactly one candidate has positive mass on each day
(the ledger's `N−`: the degenerate witness; contrast `bliHistory_tent_two_states`).
Source: Appendix B (`main.tex:447`); mandate M2 (ledger note)
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem b0_unique_state (n : ℕ) :
    ∃! q, q ∈ c.states (n + 1) ∧ 0 < superbelief (b0History Q 𝓜 c) n q := by
  have hD : degAt 𝓜.d (actualTable smallIndex Q n) (n + 1) ∈ grid smallIndex 𝓜.d (n + 1) :=
    degAt_mem_grid 𝓜.d _ (Nat.lt_succ_self n)
  refine ⟨c.code (n + 1) (degAt 𝓜.d (actualTable smallIndex Q n) (n + 1)),
    ⟨c.code_mem_states hD, ?_⟩, ?_⟩
  · unfold superbelief b0History
    rw [b0Price_stateAtom c Q (Nat.lt_succ_self n) (c.code_mem_states hD), if_pos rfl]
    norm_num
  · rintro q ⟨hq, hpos⟩
    unfold superbelief b0History at hpos
    rw [b0Price_stateAtom c Q (Nat.lt_succ_self n) hq] at hpos
    split_ifs at hpos with e
    · exact e
    · simp at hpos

/-! ## `E2xScoped → FaithMarginalScoped` and the "simplified BLI" (M7 (ii)/(iv)) -/

/-- **Faith in a written-out state implies faith in the marginal** (bli-slides-015 (a)):
`E2xScoped` gives `FaithMarginalScoped` by summing constraint 2 over the states whose table
prices `φ` at `x`. A `Finset.sum_congr`.
Source: bli-slides-015 (a)/(b); mandate M7 (ii)
Kind: L
Fidelity: exact (on the scoped predicates) -/
theorem faithMarginalScoped_of_e2xScoped {S : StateSystem} {P : History} (h : E2xScoped c S P) :
    FaithMarginalScoped c S P := by
  intro n m hnm φ hφ hno x
  unfold marginalJoint marginalMass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.mem_filter] at hq
  rw [h n m hnm q hq.1 φ hφ hno, hq.2]

/-- **The "simplified BLI" does not exclude B0** (bli-slides-015 (c)): on the denominator grid
B0 satisfies `E1x ∧ FaithMarginalScoped ∧ E3Scoped ∧ E4 ∧ E5`. Replacing constraint 2 by faith
in the marginal excludes the degenerate solution no better than constraints 1–4 do.
Source: bli-slides-015 (c); mandate M7 (iv)
Kind: C
Fidelity: weaker: scoped faith predicates; `E4` on the denominator grid
Hyps: (a) `hgrid` -/
theorem b0_simplified_bli (hgrid : ∀ n φ, φ ∈ smallSet n → Q n φ ∈ gridVals (𝓜.d (n + 1))) :
    E1x (ratHistory Q) (b0History Q 𝓜 c) ∧
      FaithMarginalScoped c (bliStateSystem Q 𝓜 c) (b0History Q 𝓜 c) ∧
      E3Scoped c (bliStateSystem Q 𝓜 c) (b0History Q 𝓜 c) ∧
      E4 (bliStateSystem Q 𝓜 c) (b0History Q 𝓜 c) ∧
      E5 (bliStateSystem Q 𝓜 c) (b0History Q 𝓜 c) :=
  ⟨b0_small c Q, faithMarginalScoped_of_e2xScoped c (b0_cond2_scoped c Q), b0_cond3_scoped c Q,
    b0_balance c Q hgrid, b0_partition c Q⟩

end Cleanroom.Bli.BliTrajectory
