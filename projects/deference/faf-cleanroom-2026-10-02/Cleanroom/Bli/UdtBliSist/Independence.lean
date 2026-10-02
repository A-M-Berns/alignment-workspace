import Cleanroom.Bli.UdtBliSist.Skeleton
import Cleanroom.Bli.BliSuperbelief.Face

/-!
# `udt-bli-sist` · Independence: non-degeneracy versus independence (T7, U12)

**Setting.** A prior `P` on day `m` with an **action coordinate** `act : Ω → A` and an action
sentence `φ₀ ∈ 𝒮.S m` for one action `a₀`, small in the sense `small ω φ₀ = true ↔ act ω = a₀`
(`ActSmall`). Faith then says `μ(state = T ∧ act = a₀) = T φ₀ · μ(state = T)` (`jointAct_eq`).

* **The Bayes lemma** (bli-soto-a-2-009 (i)): at a table of positive mass, if the **branch clause**
  of `C(n,m)` holds (`μ(state = T | act = a)` is the same for every action), then the table prices
  the action sentence at the prior's marginal, `T φ₀ = μ(act = a₀)` (`price_eq_of_branchClause`);
  conversely, if every action's sentence is priced at its marginal, the branch clause holds
  (`branchClause_of_prices`); `bayes_iff` is the two-way form for a family of sentences.
* **Face constancy ⟹ certainty** (U12): if the carrier is the product face over a day-`n` base `t`
  and *every* face table has positive mass (the finite `FS`), the branch clause forces
  `t ψ = μ(act = a₀) ∈ {0, 1}` by `bli-superbelief`'s `faceConst_prod` (`certain_of_branchClause`);
  with a second action of positive mass this is a contradiction (`fs_branchClause_impossible`).
  **Balance of the state law is not used**: only full support on the face.
* **The artifact check** (the "genuine trade-off"): over `t₀ = (p ↦ 1/2)` on `witIndex`, a prior
  supported on the three `p = 1/2` tables satisfies the branch clause and fails `NonDegenerate`
  (`Thin`), while the tent prior is non-degenerate and fails the branch clause (`Fat`); each side
  separately satisfiable, both at a non-`0/1` base price.
* **Soto's re-weighting** (bli-soto-a-2-009 (ii), bli-soto-b-2-002 (iii)): `μ'(ω) := μ(ω) ·
  μ(state) · μ(act) / μ(state ∧ act)` is a probability, satisfies the branch clause, preserves every
  within-cell conditional expectation, and **keeps faith for the action sentence iff the tables
  already price the action at the prior's marginal** (`reweight_faith_iff`) — the trade-off again,
  which is the Bayes lemma read backwards.

Sources: bli-soto-a-071, bli-soto-a-072, bli-soto-a-2-009, bli-soto-b-2-002, [[bli-program]] §3.9
U12, mandate T7.
-/

namespace Cleanroom.Bli.UdtBliSist

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.BliSuperbelief Finset

/-! ## The action coordinate and the branch clause -/

section Act

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [DecidableEq A]
variable (P : FiniteBLIPrior 𝒮 m 𝒟 A) (act : P.Ω → A)

/-- `μ(act = a)`: the prior's marginal of the action.
Source: bli-soto-a-2-009 (i) (`P(A_m = a)`)
Kind: D
Fidelity: exact -/
def actMass (a : A) : ℚ := massOf P.μ (fun ω => act ω = a)

/-- `μ(state = T ∧ act = a)`.
Source: bli-soto-a-2-009 (i)
Kind: D
Fidelity: exact -/
def jointAct (T : ↥𝒟) (a : A) : ℚ := massOf P.μ (fun ω => P.state ω = T ∧ act ω = a)

/-- **The action sentence is small**: the world's truth value of `φ₀` is `act = a₀`.
Source: mandate T7 (`PointIsSmall`); [[bli-program]] §3.9 U12 ("`A_m = a` small")
Kind: D
Fidelity: exact -/
def ActSmall (φ₀ : ↥(𝒮.S m)) (a₀ : A) : Prop := ∀ ω, P.small ω φ₀ = true ↔ act ω = a₀

/-- **The branch clause of `C(n,m)` at a table**: `μ(state = T | act = a)` does not depend on `a`.
Source: bli-soto-a-071 (`C(n,m)` (b): "does not modify the relative probabilities of the
possible `Q_n`"); bli-soto-b-2-002 (b)
Kind: D
Fidelity: exact (with the junk convention at a null action; the theorems assume positivity) -/
def BranchClause (T : ↥𝒟) : Prop :=
  ∀ a b : A, jointAct P act T a / actMass P act a = jointAct P act T b / actMass P act b

/-- **Faith on the action sentence**: `μ(state = T ∧ act = a₀) = T φ₀ · μ(state = T)`.
Source: [[bli-program]] §3.9 U12 (`E2x` applied to the action sentence)
Kind: C (the `faith` field with the small sentence read through `ActSmall`)
Fidelity: exact
Hyps: (a) `ActSmall`; uses faith -/
theorem jointAct_eq {φ₀ : ↥(𝒮.S m)} {a₀ : A} (hs : ActSmall P act φ₀ a₀) (T : ↥𝒟) :
    jointAct P act T a₀ = T.1 φ₀ * P.stateMass T := by
  have hf := P.faith T φ₀
  unfold jointAct FiniteBLIPrior.stateMass massOf
  rw [← hf]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hT : P.state ω = T
  · simp only [hT, true_and, if_true]
    by_cases ha : act ω = a₀
    · rw [if_pos ha, (hs ω).mpr ha, ind_true, mul_one]
    · rw [if_neg ha]
      have : P.small ω φ₀ = false := by
        cases h : P.small ω φ₀
        · rfl
        · exact absurd ((hs ω).mp h) ha
      rw [this, ind_false, mul_zero]
  · simp [hT]

/-- The joint masses of a table sum to its mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_jointAct [Fintype A] (T : ↥𝒟) : ∑ a, jointAct P act T a = P.stateMass T := by
  unfold jointAct FiniteBLIPrior.stateMass
  exact (massOf_fiberwise P.μ _ act).symm

/-- The action masses sum to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_actMass [Fintype A] : ∑ a, actMass P act a = 1 := by
  unfold actMass
  have := massOf_fiberwise P.μ (fun _ => True) act
  simp only [true_and] at this
  rw [← this]
  exact P.massOf_true

/-- `jointAct ≤ actMass`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jointAct_le_actMass (T : ↥𝒟) (a : A) : jointAct P act T a ≤ actMass P act a := by
  unfold jointAct actMass massOf
  apply Finset.sum_le_sum
  intro ω _
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd h1.2 h2
  · exact P.μ_nonneg ω
  · exact le_rfl

/-- **The Bayes lemma, forward**: under the branch clause at a table of positive mass, with every
action of positive mass, the table prices the action sentence at the prior's marginal:
`T φ₀ = μ(act = a₀)`.
Source: bli-soto-a-2-009 (i) ("`P(Q_n = q | A_m = a)` is constant in `a` … iff
`ext(q)(A_m = a) = P(A_m = a)`"); mandate T7(a)
Kind: C (faith on the action sentence, the law of total probability over the actions)
Fidelity: exact
Hyps: (a) `ActSmall`, the branch clause, positivity; uses faith -/
theorem price_eq_of_branchClause [Fintype A] [Nonempty A] {φ₀ : ↥(𝒮.S m)} {a₀ : A}
    (hs : ActSmall P act φ₀ a₀) (hpos : ∀ a, 0 < actMass P act a) (T : ↥𝒟)
    (hT : 0 < P.stateMass T) (hbc : BranchClause P act T) : T.1 φ₀ = actMass P act a₀ := by
  -- the common value of the branch conditionals is `stateMass T`
  set κ := jointAct P act T a₀ / actMass P act a₀ with hκ
  have hall : ∀ a, jointAct P act T a = κ * actMass P act a := by
    intro a
    rw [hκ, hbc a₀ a, div_mul_cancel₀ _ (ne_of_gt (hpos a))]
  have hsum : P.stateMass T = κ := by
    rw [← sum_jointAct P act T]
    simp only [hall]
    rw [← Finset.mul_sum, sum_actMass, mul_one]
  have h1 := hall a₀
  rw [jointAct_eq P act hs T, ← hsum] at h1
  have := mul_right_cancel₀ (ne_of_gt hT) (h1.trans (mul_comm _ _))
  exact this

/-- **The Bayes lemma, backward**: if every action's sentence is priced by `T` at the prior's
marginal, the branch clause holds at `T`.
Source: bli-soto-a-2-009 (i); mandate T7(a)
Kind: C
Fidelity: exact
Hyps: (a) `ActSmall` for every action; uses faith -/
theorem branchClause_of_prices (φ : A → ↥(𝒮.S m)) (hs : ∀ a, ActSmall P act (φ a) a)
    (hpos : ∀ a, 0 < actMass P act a) (T : ↥𝒟) (hp : ∀ a, T.1 (φ a) = actMass P act a) :
    BranchClause P act T := by
  intro a b
  rw [jointAct_eq P act (hs a) T, jointAct_eq P act (hs b) T, hp a, hp b,
    mul_div_cancel_left₀ _ (ne_of_gt (hpos a)), mul_div_cancel_left₀ _ (ne_of_gt (hpos b))]

/-- **The Bayes lemma (two-way)**: with a small sentence per action, the branch clause at a
table of positive mass holds iff the table prices every action at the prior's marginal.
Source: bli-soto-a-2-009 (i); [[bli-program]] §3.9 U12 (the displayed equivalence)
Kind: C
Fidelity: exact
Hyps: (a) `ActSmall` for every action, positivity; uses faith -/
theorem bayes_iff [Fintype A] [Nonempty A] (φ : A → ↥(𝒮.S m)) (hs : ∀ a, ActSmall P act (φ a) a)
    (hpos : ∀ a, 0 < actMass P act a) (T : ↥𝒟) (hT : 0 < P.stateMass T) :
    BranchClause P act T ↔ ∀ a, T.1 (φ a) = actMass P act a :=
  ⟨fun hbc a => price_eq_of_branchClause P act (hs a) hpos T hT hbc,
    fun hp => branchClause_of_prices P act φ hs hpos T hp⟩

end Act

/-! ## Face constancy ⟹ certainty (U12) -/

section Face

variable {𝒮 : SmallIndex} {n : ℕ} {d : ℕ → ℕ} {t : Table 𝒮 n} {A : Type} [DecidableEq A]
  [Fintype A] [Nonempty A]
variable (P : FiniteBLIPrior 𝒮 (n + 1) (faceProd 𝒮 d n t) A) (act : P.Ω → A)

/-- The day-`n` sentence `ψ` read on day `n + 1`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def liftS (ψ : ↥(𝒮.S n)) : ↥(𝒮.S (n + 1)) := ⟨ψ.1, 𝒮.mono n ψ.2⟩

/-- **Face constancy ⟹ the base is certain of the action** (U12, the one-pair theorem): on the
product face over `t` with every face table of positive mass (the finite `FS`), every action of
positive mass, and the action sentence `ψ` (a day-`n` sentence) small for `a₀`, the branch clause
at every table forces `t ψ = μ(act = a₀)` **and** `μ(act = a₀) ∈ {0, 1}` — by the Bayes lemma at
every face point and `bli-superbelief`'s `faceConst_prod`. Balance of the state law is not needed.
Source: bli-soto-a-2-009 (i) + [[bli-program]] §3.9 U12 ("under `FS` the coordinate is constant
on the face, hence `0/1` … the base is already certain of the action"); mandate T7(b)
Kind: C (`price_eq_of_branchClause` at every face point, then `faceConst_prod`)
Fidelity: exact (the carrier *is* the face, so support = face is the positivity hypothesis)
Hyps: (a) `0 < d (n+1)`, `FS`, positivity of the actions, `ActSmall`, the branch clause; uses faith -/
theorem certain_of_branchClause (hd : 0 < d (n + 1)) {ψ : ↥(𝒮.S n)} {a₀ : A}
    (hs : ActSmall P act (liftS ψ) a₀) (hFS : ∀ T : ↥(faceProd 𝒮 d n t), 0 < P.stateMass T)
    (hpos : ∀ a, 0 < actMass P act a) (hbc : ∀ T, BranchClause P act T) :
    t ψ = actMass P act a₀ ∧ (actMass P act a₀ = 0 ∨ actMass P act a₀ = 1) := by
  apply faceConst_prod hd t ψ (actMass P act a₀)
  intro Q hQ
  have := price_eq_of_branchClause P act hs hpos ⟨Q, hQ⟩ (hFS ⟨Q, hQ⟩) (hbc ⟨Q, hQ⟩)
  rw [Table.restrict_apply]
  exact this

/-- **`FS ∧ C(n,m)`-branch-clause ∧ positivity is unsatisfiable** with two actions: the certainty
`μ(act = a₀) ∈ {0, 1}` contradicts `0 < μ(act = a₀) < 1` (another action has positive mass).
Source: [[bli-program]] §3.9 U12 ("the base is already certain of the action"); mandate T7(b)
("state it … as the impossibility")
Kind: C
Fidelity: exact
Hyps: (a) as `certain_of_branchClause`, plus a second action; uses faith -/
theorem fs_branchClause_impossible (hd : 0 < d (n + 1)) {ψ : ↥(𝒮.S n)} {a₀ b₀ : A} (hab : a₀ ≠ b₀)
    (hs : ActSmall P act (liftS ψ) a₀) (hFS : ∀ T : ↥(faceProd 𝒮 d n t), 0 < P.stateMass T)
    (hpos : ∀ a, 0 < actMass P act a) (hbc : ∀ T, BranchClause P act T) : False := by
  obtain ⟨_, h01⟩ := certain_of_branchClause P act hd hs hFS hpos hbc
  have hsum := sum_actMass P act
  have hle : actMass P act a₀ + actMass P act b₀ ≤ 1 := by
    rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ a₀),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b₀⟩)]
    have : 0 ≤ ∑ a ∈ (univ.erase a₀).erase b₀, actMass P act a :=
      Finset.sum_nonneg (fun a _ => le_of_lt (hpos a))
    linarith
  have ha := hpos a₀
  have hb := hpos b₀
  rcases h01 with h0 | h1
  · rw [h0] at ha; exact lt_irrefl _ ha
  · linarith

end Face

/-! ## Superbelief ⊗ world-law priors (for the artifact checks) -/

section Sb

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [DecidableEq A]
variable (F : ↥𝒟 → ℚ) (hF0 : ∀ T, 0 ≤ F T) (hF1 : ∑ T, F T = 1) (W : WorldLaw 𝒮 m)
  (hunit : ∀ T : ↥𝒟, T.1.InUnit) (pp₀ : ↥𝒟 × W.World → Policy 𝒟 A) (U₀ : ↥𝒟 × W.World → ℚ)

/-- **A prior from a state law and a world law**: `Ω = ↥𝒟 × World`, `μ (T, w) = F T · law T w`,
`state = fst`, `small = truth ∘ snd`; faith is derived from the world law's marginal (the
`ofSkeleton` construction without the trajectory).
Source: mandate T7(c) (priors on a face with chosen support); `udt-bli-core`'s `WorldLaw`
Kind: D
Fidelity: exact -/
def sbPrior : FiniteBLIPrior 𝒮 m 𝒟 A where
  Ω := ↥𝒟 × W.World
  μ := fun ω => F ω.1 * W.law ω.1.1 ω.2
  μ_nonneg := fun ω => mul_nonneg (hF0 ω.1) (W.nonneg _ (hunit ω.1) ω.2)
  μ_sum_one := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, W.sum_one, mul_one]
    exact hF1
  state := fun ω => ω.1
  pp := pp₀
  U := U₀
  small := fun ω => W.truth ω.2
  faith := by
    intro T φ
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T' _
    by_cases h : T' = T
    · subst h
      simp only [if_true, mul_assoc, ← Finset.mul_sum, W.marginal, W.sum_one]
      ring
    · simp [h]

/-- The state mass of `sbPrior` is `F`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateMass_sbPrior (T : ↥𝒟) : (sbPrior F hF0 hF1 W hunit pp₀ U₀).stateMass T = F T := by
  unfold FiniteBLIPrior.stateMass massOf
  change (∑ ω : ↥𝒟 × W.World, if ω.1 = T then F ω.1 * W.law ω.1.1 ω.2 else 0) = F T
  rw [Fintype.sum_prod_type, Finset.sum_eq_single T]
  · simp only [if_true, ← Finset.mul_sum, W.sum_one, mul_one]
  · intro T' _ hT'; simp [hT']
  · intro h; exact absurd (Finset.mem_univ _) h

end Sb

section SbBool

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)}
variable (F : ↥𝒟 → ℚ) (hF0 : ∀ T, 0 ≤ F T) (hF1 : ∑ T, F T = 1) (W : WorldLaw 𝒮 m)
  (hunit : ∀ T : ↥𝒟, T.1.InUnit) (pp₀ : ↥𝒟 × W.World → Policy 𝒟 Bool)
  (U₀ : ↥𝒟 × W.World → ℚ)

/-- With the action the world's truth of `φ₀`, `μ(state = T ∧ act = true) = F T · T φ₀`.
Source: none: infrastructure (faith on the action sentence, explicitly)
Kind: L
Fidelity: n/a -/
lemma jointAct_sbPrior_true (φ₀ : ↥(𝒮.S m)) (T : ↥𝒟) :
    jointAct (sbPrior F hF0 hF1 W hunit pp₀ U₀) (fun ω => W.truth ω.2 φ₀) T true =
      F T * T.1 φ₀ := by
  unfold jointAct massOf
  change (∑ ω : ↥𝒟 × W.World, if ω.1 = T ∧ W.truth ω.2 φ₀ = true then F ω.1 * W.law ω.1.1 ω.2
    else 0) = F T * T.1 φ₀
  rw [Fintype.sum_prod_type, Finset.sum_eq_single T]
  · simp only [true_and]
    rw [← W.marginal T.1 φ₀, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    by_cases h : W.truth w φ₀ = true
    · simp [h]
    · simp [h]
  · intro T' _ hT'; simp [hT']
  · intro h; exact absurd (Finset.mem_univ _) h

/-- With the action the world's truth of `φ₀`, `μ(state = T ∧ act = false) = F T · (1 − T φ₀)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jointAct_sbPrior_false (φ₀ : ↥(𝒮.S m)) (T : ↥𝒟) :
    jointAct (sbPrior F hF0 hF1 W hunit pp₀ U₀) (fun ω => W.truth ω.2 φ₀) T false =
      F T * (1 - T.1 φ₀) := by
  have h := sum_jointAct (sbPrior F hF0 hF1 W hunit pp₀ U₀) (fun ω => W.truth ω.2 φ₀) T
  rw [Fintype.sum_bool, jointAct_sbPrior_true, stateMass_sbPrior] at h
  linarith

/-- The action `truth of φ₀` is small for `true` with sentence `φ₀`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma actSmall_sbPrior (φ₀ : ↥(𝒮.S m)) :
    ActSmall (sbPrior F hF0 hF1 W hunit pp₀ U₀) (fun ω => W.truth ω.2 φ₀) φ₀ true :=
  fun _ => Iff.rfl

end SbBool

/-! ## The artifact check over `t₀` on `witIndex` -/

namespace Artifact

open Cleanroom.Bli.UdtBliCore.Tent

/-- The product face over `t₀` on `witIndex` (the whole 9-table grid, `faceProd_t₀`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev Face : Finset (Table witIndex 1) := faceProd witIndex witMesh.d 0 t₀

/-- Every face table is in the unit cube.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma face_inUnit (T : ↥Face) : T.1.InUnit :=
  inUnit_of_mem_grid (faceProd_subset_grid _ _ T.2)

/-- **The thin state law**: `3 · tentLaw t₀` on the three `p = 1/2` tables, `0` elsewhere — a
probability on the face supported on a proper subset of it.
Source: mandate T7(c) ("support a proper subset of the face on which `φ_a` is constant")
Kind: D
Fidelity: exact -/
def thinF (T : ↥Face) : ℚ := if T.1 pW1 = 1 / 2 then 3 * tentLaw witMesh 0 t₀ T.1 else 0

/-- `thinF ≥ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma thinF_nonneg (T : ↥Face) : 0 ≤ thinF T := by
  unfold thinF; split_ifs
  · have := tentLaw_nonneg (𝓜 := witMesh) t₀ T.1; linarith
  · exact le_rfl

/-- `∑ thinF = 1` (three tables of mass `1/9`, tripled: by the coin-class sum, not by counting).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma thinF_sum : ∑ T, thinF T = 1 := by
  unfold thinF
  rw [Finset.sum_coe_sort Face (fun Q => if Q pW1 = 1 / 2 then 3 * tentLaw witMesh 0 t₀ Q else 0)]
  change (∑ Q ∈ faceProd witIndex witMesh.d 0 t₀, if Q pW1 = 1 / 2 then 3 * tentLaw witMesh 0 t₀ Q
    else 0) = 1
  rw [faceProd_t₀]
  have := TentSist.sum_grid_coin_tentLaw (1 / 2) half_mem_gridVals_two
  have e : ∀ Q, (if Q pW1 = 1 / 2 then 3 * tentLaw witMesh 0 t₀ Q else 0) =
      3 * (if Q pW1 = 1 / 2 then tentLaw witMesh 0 t₀ Q else 0) := by
    intro Q; split_ifs <;> ring
  simp only [e]
  rw [← Finset.mul_sum, this]
  norm_num

/-- **The thin prior**: the thin state law with the product world law and the action "`p` is
true in the world".
Source: mandate T7(c)
Kind: D
Fidelity: exact -/
abbrev thinPrior : FiniteBLIPrior witIndex 1 Face Bool :=
  sbPrior thinF thinF_nonneg thinF_sum (productWorldLaw witIndex 1) face_inUnit
    (fun _ _ => true) (fun _ => 0)

/-- The thin prior's action coordinate: the world's truth of `p`.
Source: mandate T7 (`act` as a coordinate)
Kind: D
Fidelity: exact -/
abbrev thinAct (ω : thinPrior.Ω) : Bool := (productWorldLaw witIndex 1).truth ω.2 pW1

/-- **The thin prior satisfies the branch clause at every table** (every supported table prices
`p` at `1/2`, the prior's marginal) **and fails `NonDegenerate`** (the face table `(1, 1/2)` has
mass `0`), at the interior base price `t₀ p = 1/2`, **with both actions of mass `1/2`** (the
positivity clause `fs_branchClause_impossible` needs, exported since repair round 1) — the
"genuine trade-off", first side.
Source: [[bli-program]] §3.9 U12 ("without `FS`, restricting the support satisfies `C(n,m)` at the
price of degeneracy on that coordinate"); mandate T7(c)
Kind: N+
Fidelity: exact
Hyps: (a) none; uses faith (through the world law's marginal) -/
theorem thin_branchClause_not_nonDegenerate :
    (∀ T, BranchClause thinPrior thinAct T) ∧
      (∀ a, actMass thinPrior thinAct a = 1 / 2) ∧
      ¬ NonDegenerate witMesh.d (fun Q => if h : Q ∈ Face then thinF ⟨Q, h⟩ else 0) t₀ ∧
      ¬ (t₀ ⟨pW, pW_mem_S0⟩ = 0 ∨ t₀ ⟨pW, pW_mem_S0⟩ = 1) := by
  have hj : ∀ (T : ↥Face) (a : Bool), jointAct thinPrior thinAct T a = thinF T * (1 / 2) := by
    intro T a
    cases a
    · rw [jointAct_sbPrior_false]
      unfold thinF
      split_ifs with h
      · rw [h]; ring
      · ring
    · rw [jointAct_sbPrior_true]
      unfold thinF
      split_ifs with h
      · rw [h]
      · ring
  have hsplit : ∀ a, actMass thinPrior thinAct a = ∑ T, jointAct thinPrior thinAct T a := by
    intro a
    unfold actMass jointAct
    have := massOf_fiberwise thinPrior.μ (fun ω => thinAct ω = a) thinPrior.state
    rw [this]
    apply Finset.sum_congr rfl
    intro T _
    apply massOf_congr
    intro ω
    exact and_comm
  have hm : ∀ a, actMass thinPrior thinAct a = 1 / 2 := by
    intro a
    have hsum := sum_actMass thinPrior thinAct
    have h1 : actMass thinPrior thinAct true = actMass thinPrior thinAct false := by
      rw [hsplit, hsplit]
      apply Finset.sum_congr rfl
      intro T _
      rw [hj, hj]
    rw [Fintype.sum_bool, h1] at hsum
    cases a
    · linarith
    · linarith
  refine ⟨?_, hm, ?_, ?_⟩
  · intro T a b
    rw [hj, hj, hm, hm]
  · intro hnd
    have hmem : Qone ∈ Face := by
      show Qone ∈ faceProd witIndex witMesh.d 0 t₀
      rw [faceProd_t₀]; exact Qone_mem_grid
    have := hnd Qone hmem
    dsimp only at this
    rw [dif_pos hmem] at this
    unfold thinF at this
    have h1 : Qone pW1 = 1 := by simp [Qone]
    simp only [Subtype.coe_mk, h1] at this
    norm_num at this
  · unfold t₀; norm_num

/-- **The fat state law**: the tent law at `t₀` (every face table has mass `1/9`).
Source: mandate T7(c) ("the tent at `t₀`")
Kind: D
Fidelity: exact -/
def fatF (T : ↥Face) : ℚ := tentLaw witMesh 0 t₀ T.1

/-- `fatF ≥ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fatF_nonneg (T : ↥Face) : 0 ≤ fatF T := tentLaw_nonneg t₀ T.1

/-- `∑ fatF = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fatF_sum : ∑ T, fatF T = 1 := by
  unfold fatF
  rw [Finset.sum_coe_sort Face (fun Q => tentLaw witMesh 0 t₀ Q)]
  change (∑ Q ∈ faceProd witIndex witMesh.d 0 t₀, tentLaw witMesh 0 t₀ Q) = 1
  rw [faceProd_t₀]
  exact sum_tentLaw_t₀

/-- **The fat prior**: the tent law with the product world law and the action "`p` is true".
Source: mandate T7(c)
Kind: D
Fidelity: exact -/
abbrev fatPrior : FiniteBLIPrior witIndex 1 Face Bool :=
  sbPrior fatF fatF_nonneg fatF_sum (productWorldLaw witIndex 1) face_inUnit
    (fun _ _ => true) (fun _ => 0)

/-- The fat prior's action coordinate: the world's truth of `p`.
Source: mandate T7 (`act` as a coordinate)
Kind: D
Fidelity: exact -/
abbrev fatAct (ω : fatPrior.Ω) : Bool := (productWorldLaw witIndex 1).truth ω.2 pW1

/-- **The fat prior is non-degenerate and fails the branch clause** at the table `(1, 1/2)`: there
`μ(state = T ∧ act = true) = 1/9 > 0 = μ(state = T ∧ act = false)`, while both actions have positive
mass — the "genuine trade-off", second side.
Source: [[bli-program]] §3.9 U12; mandate T7(c) ("a non-degenerate kernel at a non-`0/1` price
failing the branch clause (the tent at `t₀`)")
Kind: N+
Fidelity: exact
Hyps: (a) none; uses faith (through the world law's marginal) -/
theorem fat_nonDegenerate_not_branchClause :
    NonDegenerate witMesh.d (tentLaw witMesh 0 t₀) t₀ ∧
      (∀ a, 0 < actMass fatPrior fatAct a) ∧
      ¬ BranchClause fatPrior fatAct ⟨Qone, by
        show Qone ∈ faceProd witIndex witMesh.d 0 t₀
        rw [faceProd_t₀]; exact Qone_mem_grid⟩ := by
  have hQ1 : Qone pW1 = 1 := by simp [Qone]
  have hQ0 : Q₂ pW1 = 0 := by simp [Q₂]
  have hmem1 : Qone ∈ Face := by
    show Qone ∈ faceProd witIndex witMesh.d 0 t₀
    rw [faceProd_t₀]; exact Qone_mem_grid
  have hmem0 : Q₂ ∈ Face := by
    show Q₂ ∈ faceProd witIndex witMesh.d 0 t₀
    rw [faceProd_t₀]; exact Q₂_mem_grid
  have hjt : jointAct fatPrior fatAct ⟨Qone, hmem1⟩ true = 1 / 9 := by
    rw [jointAct_sbPrior_true]
    unfold fatF
    simp only
    rw [tentLaw_t₀ Qone_mem_grid, hQ1, mul_one]
  have hjf : jointAct fatPrior fatAct ⟨Qone, hmem1⟩ false = 0 := by
    rw [jointAct_sbPrior_false]
    unfold fatF
    simp only
    rw [hQ1]; ring
  have hjf0 : jointAct fatPrior fatAct ⟨Q₂, hmem0⟩ false = 1 / 9 := by
    rw [jointAct_sbPrior_false]
    unfold fatF
    simp only
    rw [tentLaw_t₀ Q₂_mem_grid, hQ0]; ring
  have hpos : ∀ a, 0 < actMass fatPrior fatAct a := by
    intro a
    cases a
    · exact lt_of_lt_of_le (by rw [hjf0]; norm_num) (jointAct_le_actMass fatPrior fatAct _ false)
    · exact lt_of_lt_of_le (by rw [hjt]; norm_num) (jointAct_le_actMass fatPrior fatAct _ true)
  refine ⟨nonDegenerate_t₀, hpos, ?_⟩
  intro hbc
  have := hbc true false
  rw [hjt, hjf, zero_div] at this
  have hpt := hpos true
  have : (1 / 9 : ℚ) / actMass fatPrior fatAct true > 0 := by positivity
  linarith

end Artifact

/-! ## Soto's re-weighting and the faith trade-off (T7 f) -/

section Reweight

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [DecidableEq A] [Fintype A]
variable (P : FiniteBLIPrior 𝒮 m 𝒟 A) (act : P.Ω → A)

/-- **Soto's re-weighting** `μ'(ω) := μ(ω) · μ(state = state ω) · μ(act = act ω) / μ(state ∧ act)`:
the joint of `(state, act)` is replaced by the product of its marginals, each `(state, act)`-cell
keeping its internal shape.
Source: bli-soto-a-2-009 (ii) (`P'(q, a, u) := P(q) · P(a) · P(u | q, a)`); bli-soto-b-2-002 (iii)
Kind: D
Fidelity: exact (finite; the cell must be positive where both marginals are — hypothesis of the
theorems) -/
def reweight (ω : P.Ω) : ℚ :=
  P.μ ω * P.stateMass (P.state ω) * actMass P act (act ω) / jointAct P act (P.state ω) (act ω)

/-- The re-weighted mass of a `(state, act)`-cell is the product of the marginals, when the cell
is positive.
Source: bli-soto-a-2-009 (ii)
Kind: L
Fidelity: exact -/
lemma reweight_cell (T : ↥𝒟) (a : A) (hpos : 0 < jointAct P act T a) :
    massOf (reweight P act) (fun ω => P.state ω = T ∧ act ω = a) =
      P.stateMass T * actMass P act a := by
  unfold massOf reweight
  have e : ∀ ω, (if P.state ω = T ∧ act ω = a then
      P.μ ω * P.stateMass (P.state ω) * actMass P act (act ω) /
        jointAct P act (P.state ω) (act ω) else 0) =
      (if P.state ω = T ∧ act ω = a then P.μ ω else 0) *
        (P.stateMass T * actMass P act a / jointAct P act T a) := by
    intro ω
    split_ifs with h
    · rw [h.1, h.2]; ring
    · ring
  simp only [e]
  rw [← Finset.sum_mul]
  change jointAct P act T a * _ = _
  rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hpos)]

/-- A `(state, act)`-cell that is null for `μ` is null for `μ'` too.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma reweight_cell_null (T : ↥𝒟) (a : A) (h : jointAct P act T a = 0) :
    massOf (reweight P act) (fun ω => P.state ω = T ∧ act ω = a) = 0 := by
  unfold massOf
  apply Finset.sum_eq_zero
  intro ω _
  split_ifs with hω
  · unfold reweight
    rw [hω.1, hω.2, h, div_zero]
  · rfl

/-- **The re-weighting is a probability and has the product joint** whenever every cell with
positive marginals is positive: `μ'(state = T ∧ act = a) = μ(state = T) · μ(act = a)` for all `T, a`,
hence `∑ μ' = 1`, `μ'(state = T) = μ(state = T)`, `μ'(act = a) = μ(act = a)`.
Source: bli-soto-a-2-009 (ii) ("satisfies the branch clause … changes only `P(a | q)`")
Kind: P
Fidelity: exact
Hyps: (a) positivity of the cells with positive marginals; does not use faith -/
theorem reweight_joint (hcell : ∀ T a, 0 < P.stateMass T → 0 < actMass P act a →
      0 < jointAct P act T a) (T : ↥𝒟) (a : A) :
    massOf (reweight P act) (fun ω => P.state ω = T ∧ act ω = a) =
      P.stateMass T * actMass P act a := by
  by_cases hT : 0 < P.stateMass T
  · by_cases ha : 0 < actMass P act a
    · exact reweight_cell P act T a (hcell T a hT ha)
    · have hz : actMass P act a = 0 :=
        le_antisymm (not_lt.mp ha) (massOf_nonneg _ P.μ_nonneg _)
      rw [hz, mul_zero]
      apply reweight_cell_null
      exact le_antisymm (hz ▸ jointAct_le_actMass P act T a) (massOf_nonneg _ P.μ_nonneg _)
  · have hz : P.stateMass T = 0 := le_antisymm (not_lt.mp hT) (P.stateMass_nonneg T)
    rw [hz, zero_mul]
    apply reweight_cell_null
    have hle : jointAct P act T a ≤ P.stateMass T := by
      rw [← sum_jointAct P act T]
      exact Finset.single_le_sum (fun b _ => massOf_nonneg _ P.μ_nonneg _) (Finset.mem_univ a)
    exact le_antisymm (hz ▸ hle) (massOf_nonneg _ P.μ_nonneg _)

/-- The re-weighted state mass is the original.
Source: bli-soto-a-2-009 (ii)
Kind: L
Fidelity: exact -/
lemma reweight_stateMass (hcell : ∀ T a, 0 < P.stateMass T → 0 < actMass P act a →
      0 < jointAct P act T a) (T : ↥𝒟) :
    massOf (reweight P act) (fun ω => P.state ω = T) = P.stateMass T := by
  rw [massOf_fiberwise (reweight P act) _ act]
  simp only [reweight_joint P act hcell T]
  rw [← Finset.mul_sum, sum_actMass, mul_one]

/-- **The re-weighting satisfies the branch clause**: `μ'(state = T | act = a) = μ(state = T)` for
every action of positive mass.
Source: bli-soto-a-2-009 (ii); bli-soto-b-2-002 (iii)
Kind: P
Fidelity: exact
Hyps: (a) as `reweight_joint`; does not use faith -/
theorem reweight_branchClause (hcell : ∀ T a, 0 < P.stateMass T → 0 < actMass P act a →
      0 < jointAct P act T a) (hpos : ∀ a, 0 < actMass P act a) (T : ↥𝒟) (a b : A) :
    massOf (reweight P act) (fun ω => P.state ω = T ∧ act ω = a) /
        massOf (reweight P act) (fun ω => act ω = a) =
      massOf (reweight P act) (fun ω => P.state ω = T ∧ act ω = b) /
        massOf (reweight P act) (fun ω => act ω = b) := by
  have hact : ∀ a, massOf (reweight P act) (fun ω => act ω = a) = actMass P act a := by
    intro a
    rw [massOf_fiberwise (reweight P act) _ P.state]
    have e : ∀ T, massOf (reweight P act) (fun ω => act ω = a ∧ P.state ω = T) =
        P.stateMass T * actMass P act a := by
      intro T
      rw [← reweight_joint P act hcell T a]
      apply massOf_congr; intro ω; exact and_comm
    simp only [e]
    rw [← Finset.sum_mul, P.sum_stateMass, one_mul]
  rw [reweight_joint P act hcell, reweight_joint P act hcell, hact, hact,
    mul_div_assoc, mul_div_assoc, div_self (ne_of_gt (hpos a)), div_self (ne_of_gt (hpos b))]

/-- **The re-weighting preserves every within-cell conditional expectation**: on a positive cell,
`𝔼_{μ'}[f | state = T ∧ act = a] = 𝔼_μ[f | state = T ∧ act = a]`.
Source: bli-soto-a-2-009 (ii) ("preserves every within-branch conditional `P(u | q, a)`")
Kind: P
Fidelity: exact
Hyps: (a) positivity of the cell; does not use faith -/
theorem reweight_condExp (f : P.Ω → ℚ) (T : ↥𝒟) (a : A) (hpos : 0 < jointAct P act T a) :
    condExp (reweight P act) f (fun ω => P.state ω = T ∧ act ω = a) =
      condExp P.μ f (fun ω => P.state ω = T ∧ act ω = a) := by
  unfold condExp
  rw [reweight_cell P act T a hpos]
  have e : integralOf (reweight P act) f (fun ω => P.state ω = T ∧ act ω = a) =
      integralOf P.μ f (fun ω => P.state ω = T ∧ act ω = a) *
        (P.stateMass T * actMass P act a / jointAct P act T a) := by
    unfold integralOf reweight
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs with h
    · rw [h.1, h.2]; ring
    · ring
  rw [e]
  change _ = integralOf P.μ f _ / jointAct P act T a
  have hT : 0 < P.stateMass T := by
    have h2 : jointAct P act T a ≤ P.stateMass T := by
      rw [← sum_jointAct P act T]
      exact Finset.single_le_sum (fun b _ => massOf_nonneg _ P.μ_nonneg _) (Finset.mem_univ a)
    linarith
  have ha : 0 < actMass P act a := lt_of_lt_of_le hpos (jointAct_le_actMass P act T a)
  field_simp

/-- **The faith trade-off**: for the action sentence `φ₀` (small for `a₀`), the re-weighted law
satisfies the faith identity at a table `T` of positive mass **iff** `T φ₀ = μ(act = a₀)` — the
tables must already price the action at the prior's marginal (the Bayes lemma read backwards).
So "modify the conditionals to enforce `C(n,m)`" breaks faith exactly where the branch clause
failed before the edit.
Source: bli-soto-a-2-009 (ii) and bli-soto-b-2-002 (iii)'s suspicious flag ("may be inconsistent
with self-trust, as Soto half-admits"); mandate T7(f), §5.9
Kind: P
Fidelity: exact
Hyps: (a) `ActSmall`, positivity of the cells with positive marginals, `0 < stateMass T`; uses faith
(of `μ`, through `jointAct_eq`) -/
theorem reweight_faith_iff (hcell : ∀ T a, 0 < P.stateMass T → 0 < actMass P act a →
      0 < jointAct P act T a) {φ₀ : ↥(𝒮.S m)} {a₀ : A} (hs : ActSmall P act φ₀ a₀) (T : ↥𝒟)
    (hT : 0 < P.stateMass T) :
    (integralOf (reweight P act) (fun ω => ind (P.small ω φ₀)) (fun ω => P.state ω = T) =
        T.1 φ₀ * massOf (reweight P act) (fun ω => P.state ω = T)) ↔
      T.1 φ₀ = actMass P act a₀ := by
  have hint : integralOf (reweight P act) (fun ω => ind (P.small ω φ₀)) (fun ω => P.state ω = T) =
      massOf (reweight P act) (fun ω => P.state ω = T ∧ act ω = a₀) := by
    rw [← massOf_and_true_eq_integralOf_ind]
    apply massOf_congr
    intro ω
    exact and_congr_right (fun _ => hs ω)
  rw [hint, reweight_joint P act hcell, reweight_stateMass P act hcell]
  constructor
  · intro h
    exact (mul_left_cancel₀ (ne_of_gt hT) (h.trans (mul_comm _ _))).symm
  · intro h
    rw [h]; ring

end Reweight

end Cleanroom.Bli.UdtBliSist
