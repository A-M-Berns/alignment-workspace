import Cleanroom.Udt.UdtPaperTiling.Vingean

/-!
# `udt-paper-tiling` · Collapse: the extensional reading of Theorem 3 is empty (T6)

bli-paper-017(a), as theorems. Under the **extensional reading** — every argmax-term evaluated at
the meta level, i.e. the computation-output variables of `Vingean.lean` taken *constant* — the
assumptions of Theorem 3 lose their content:

* `faithInJointArgmaxAt_const_iff`, `exists_jointMaximizer`, `faithInJointArgmax_extensional`:
  with `αJ` constant, Faith in Joint Argmax says exactly that the constant is a meta-level joint
  maximizer, and such a constant exists in **every** model with a positive cell — FJA holds in
  every model when the argmax variable is a constant maximizer (`max ≥ max`). The same for Faith
  in Argmax (`faithInArgmax_const_iff`, `faithInArgmax_extensional`).
* `actionCoordination_const_iff`, `naiveActionCoordination_const_iff`: with constant variables,
  Action Coordination is the equation `aK = aK'` between two constants.
* `kdp_const_null`, `kdp_const_fairness_cell_null`: with `αM ō` constant `aK'`, Knowledge of
  Decision Procedure makes every point `pp · ō = a ≠ aK'` null, so for `ac aₘ ≠ aK'` the right side
  of Fine-Grained Fairness and every intermediate cell of Theorem 3's chain is a null event: the
  chain is a statement about the junk value `0`.
* `kdp_all_const_pointMass`: KDP at every observation with constant variables makes `pp` a.s. the
  constant policy `c`, so `EU o a` is junk for `a ≠ c o` and "strictly prefers" compares junk zeros.

Severity: blocking for any formalization that evaluates the argmaxes at the meta level; not for
the paper, which flags the issue at `main.tex` 267 (`udt-paper-tiling-findings`, F-2).
The predicates are the same ones as in `Vingean.lean`; nothing here is a separate definition.

Package `udt-paper-tiling` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Udt.UdtPaperTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {Act : Type} [Fintype Act]
  [DecidableEq Act] {P : FiniteBLIPrior 𝒮 m 𝒟 Act}

/-! ## Faith in Joint Argmax with a constant variable -/

/-- **A meta-level joint maximizer** for `(A', o, o')`: a constant `aK` such that every positive
concrete cell `(a, a')`, `a ∈ A'`, is dominated by some positive cell `(b, aK)`, `b ∈ A'`. This is
what the paper's `argmax_{a'} max_{a ∈ A'} E_p(u | …)` denotes under the extensional reading.
Source: `main.tex` 219–225 read extensionally (bli-paper-017(a))
Kind: D
Fidelity: exact (positive cells only) -/
def IsJointMaximizer (P : FiniteBLIPrior 𝒮 m 𝒟 Act) (A' : Finset Act) (o o' : ↥𝒟) (aK : Act) :
    Prop :=
  ∀ a' : Act, ∀ a ∈ A', 0 < P.pairMass o o' a a' →
    ∃ b ∈ A', 0 < P.pairMass o o' b aK ∧ cellEU P o o' a a' ≤ cellEU P o o' b aK

/-- With `αJ` constant `aK`, the `αJ`-cell of `b` is the concrete cell `(b, aK)` (mass).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jointMass_const (V : ArgmaxVars P) {A' : Finset Act} {o o' : ↥𝒟} {aK : Act}
    (h : ∀ ω, V.αJ A' o o' ω = aK) (b : Act) : jointMass V A' o o' b = P.pairMass o o' b aK := by
  unfold jointMass FiniteBLIPrior.pairMass
  apply massOf_congr
  intro ω
  rw [h ω]

/-- With `αJ` constant `aK`, the `αJ`-cell of `b` is the concrete cell `(b, aK)` (value).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jointEU_const (V : ArgmaxVars P) {A' : Finset Act} {o o' : ↥𝒟} {aK : Act}
    (h : ∀ ω, V.αJ A' o o' ω = aK) (b : Act) : jointEU V A' o o' b = cellEU P o o' b aK := by
  unfold jointEU cellEU
  apply condExp_congr
  intro ω
  rw [h ω]

/-- **FJA with a constant variable is "the constant is a joint maximizer"**: the assumption's
content under the extensional reading is the definition of argmax.
Source: bli-paper-017(a); flags of bli-paper-010
Kind: P
Fidelity: exact
Hyps: (a) the constancy of `αJ` at the triple -/
theorem faithInJointArgmaxAt_const_iff (V : ArgmaxVars P) {A' : Finset Act} {o o' : ↥𝒟}
    {aK : Act} (h : ∀ ω, V.αJ A' o o' ω = aK) :
    FaithInJointArgmaxAt V A' o o' ↔ IsJointMaximizer P A' o o' aK := by
  unfold FaithInJointArgmaxAt IsJointMaximizer
  simp only [jointMass_const V h, jointEU_const V h]

/-- **A joint maximizer exists in every model with a positive cell**: take a cell of maximal
value among the positive cells with first coordinate in `A'`.
Source: bli-paper-017(a) ("Faith in Argmax and Faith in Joint Argmax hold in every model")
Kind: P
Fidelity: exact
Hyps: (a) some positive cell -/
theorem exists_jointMaximizer (A' : Finset Act) (o o' : ↥𝒟)
    (hne : ∃ a' a, a ∈ A' ∧ 0 < P.pairMass o o' a a') : ∃ aK, IsJointMaximizer P A' o o' aK := by
  classical
  let cells : Finset (Act × Act) :=
    Finset.univ.filter (fun p => p.1 ∈ A' ∧ 0 < P.pairMass o o' p.1 p.2)
  obtain ⟨a', a, ha, hpos⟩ := hne
  have hcne : cells.Nonempty := ⟨(a, a'), by simp [cells, ha, hpos]⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image cells (fun p => cellEU P o o' p.1 p.2) hcne
  refine ⟨p.2, fun a' a ha hpos => ⟨p.1, ?_, ?_, ?_⟩⟩
  · simp only [cells, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact hp.1
  · simp only [cells, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact hp.2
  · exact hmax (a, a') (by simp [cells, ha, hpos])

/-- **Under the extensional reading, Faith in Joint Argmax holds in every model** with a positive
cell: there is a constant value of the argmax variable for which the assumption is true,
whatever the prior.
Source: bli-paper-017(a); flags of bli-paper-010
Kind: P
Fidelity: exact
Hyps: (a) some positive cell -/
theorem faithInJointArgmax_extensional (A' : Finset Act) (o o' : ↥𝒟)
    (hne : ∃ a' a, a ∈ A' ∧ 0 < P.pairMass o o' a a') :
    ∃ aK, ∀ V : ArgmaxVars P, (∀ ω, V.αJ A' o o' ω = aK) → FaithInJointArgmaxAt V A' o o' := by
  obtain ⟨aK, hmax⟩ := exists_jointMaximizer A' o o' hne
  exact ⟨aK, fun V h => (faithInJointArgmaxAt_const_iff V h).mpr hmax⟩

/-! ## Faith in Argmax with a constant variable -/

/-- **A meta-level conditional maximizer** at `o` given `π*(o') = a'`: a constant `aK` whose cell
is positive and dominates every positive cell `(a', a)`, whenever some such cell is positive.
Source: `main.tex` 365–370 read extensionally (bli-paper-017(a))
Kind: D
Fidelity: exact (positive cells only) -/
def IsCondMaximizer (P : FiniteBLIPrior 𝒮 m 𝒟 Act) (o o' : ↥𝒟) (a' aK : Act) : Prop :=
  ∀ a : Act, 0 < P.pairMass o' o a' a →
    0 < P.pairMass o' o a' aK ∧ cellEU P o' o a' a ≤ cellEU P o' o a' aK

/-- **FA with a constant variable is "the constant is a conditional maximizer".**
Source: bli-paper-017(a); flags of bli-paper-014
Kind: P
Fidelity: exact
Hyps: (a) the constancy of `αC` at the triple -/
theorem faithInArgmax_const_iff (V : ArgmaxVars P) {o o' : ↥𝒟} {a' aK : Act}
    (h : ∀ ω, V.αC o' a' o ω = aK) : FaithInArgmax V o o' a' ↔ IsCondMaximizer P o o' a' aK := by
  unfold FaithInArgmax IsCondMaximizer
  have hm : massOf P.μ (fun ω => P.pp ω o' = a' ∧ P.pp ω o = V.αC o' a' o ω) =
      P.pairMass o' o a' aK := by
    unfold FiniteBLIPrior.pairMass
    apply massOf_congr
    intro ω
    rw [h ω]
  have hv : condExp P.μ P.U (fun ω => P.pp ω o' = a' ∧ P.pp ω o = V.αC o' a' o ω) =
      cellEU P o' o a' aK := by
    unfold cellEU
    apply condExp_congr
    intro ω
    rw [h ω]
  simp only [hm, hv]

/-- **Under the extensional reading, Faith in Argmax holds in every model** with a positive cell.
Source: bli-paper-017(a); flags of bli-paper-014
Kind: P
Fidelity: exact
Hyps: (a) some positive cell -/
theorem faithInArgmax_extensional (o o' : ↥𝒟) (a' : Act) (hne : ∃ a, 0 < P.pairMass o' o a' a) :
    ∃ aK, ∀ V : ArgmaxVars P, (∀ ω, V.αC o' a' o ω = aK) → FaithInArgmax V o o' a' := by
  classical
  let cells : Finset Act := Finset.univ.filter (fun a => 0 < P.pairMass o' o a' a)
  obtain ⟨a, hpos⟩ := hne
  have hcne : cells.Nonempty := ⟨a, by simp [cells, hpos]⟩
  obtain ⟨aK, haK, hmax⟩ := Finset.exists_max_image cells (fun a => cellEU P o' o a' a) hcne
  refine ⟨aK, fun V h => (faithInArgmax_const_iff V h).mpr fun a hpos => ⟨?_, ?_⟩⟩
  · simp only [cells, Finset.mem_filter, Finset.mem_univ, true_and] at haK
    exact haK
  · exact hmax a (by simp [cells, hpos])

/-! ## Action Coordination and KDP with constant variables -/

/-- The mass of a constant proposition is `1` or `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_const_prop (p : Prop) [Decidable p] :
    massOf P.μ (fun _ => p) = if p then 1 else 0 := by
  by_cases hp : p
  · rw [if_pos hp, ← P.massOf_true]
    exact massOf_congr P.μ (fun _ => by simp [hp])
  · rw [if_neg hp]
    unfold massOf
    simp [hp]

/-- **Action Coordination with constant variables is an equation between two constants.**
Source: bli-paper-017(a); flags of bli-paper-011
Kind: P
Fidelity: exact
Hyps: (a) the two constancies -/
theorem actionCoordination_const_iff (V : ArgmaxVars P) {A' : Finset Act} {o o' : ↥𝒟} {aK aK' : Act}
    (hJ : ∀ ω, V.αJ A' o o' ω = aK) (hM : ∀ ω, V.αM o' ω = aK') :
    ActionCoordination V A' o o' ↔ aK = aK' := by
  unfold ActionCoordination
  have : massOf P.μ (fun ω => V.αJ A' o o' ω = V.αM o' ω) = massOf P.μ (fun _ => aK = aK') :=
    massOf_congr P.μ (fun ω => by rw [hJ ω, hM ω])
  rw [this, massOf_const_prop]
  by_cases h : aK = aK' <;> simp [h]

/-- **Naive Action Coordination with constant variables is an equation between two constants.**
Source: bli-paper-017(a); flags of bli-paper-015
Kind: P
Fidelity: exact
Hyps: (a) the two constancies, `a₁ ∉ 𝒜^m` -/
theorem naiveActionCoordination_const_iff (S : PaperStructure 𝒟 Act) (V : ArgmaxVars P)
    {o₁ o₂ : ↥𝒟} {a₁ aK aK' : Act} (ha₁ : a₁ ∉ S.selfMod) (hC : ∀ ω, V.αC o₂ a₁ o₁ ω = aK)
    (hM : ∀ ω, V.αM o₁ ω = aK') : NaiveActionCoordination S V o₁ o₂ a₁ ↔ aK = aK' := by
  unfold NaiveActionCoordination
  have : massOf P.μ (fun ω => V.αC o₂ a₁ o₁ ω = V.αM o₁ ω) = massOf P.μ (fun _ => aK = aK') :=
    massOf_congr P.μ (fun ω => by rw [hC ω, hM ω])
  rw [this, massOf_const_prop]
  by_cases h : aK = aK' <;> simp [h, ha₁]

/-- **KDP with a constant variable nulls every other point**: `αM ō = aK'` constant and KDP at `ō`
give `μ(pp · ō = a) = 0` for every `a ≠ aK'`.
Source: bli-paper-017(a); flags of bli-paper-012
Kind: P
Fidelity: exact
Hyps: (a) the constancy, KDP -/
theorem kdp_const_null (V : ArgmaxVars P) {ō : ↥𝒟} {aK' : Act} (hM : ∀ ω, V.αM ō ω = aK')
    (hK : KnowledgeOfDecisionProcedure V ō) : ∀ a, a ≠ aK' → P.ppMass ō a = 0 := by
  intro a ha
  unfold KnowledgeOfDecisionProcedure at hK
  have h1 : massOf P.μ (fun ω => P.pp ω ō = aK') = 1 := by
    rw [← hK]
    exact massOf_congr P.μ (fun ω => by rw [hM ω])
  rw [massOf_eq_one_iff P.μ P.μ_sum_one] at h1
  apply le_antisymm _ (P.ppMass_nonneg ō a)
  rw [← h1]
  exact massOf_mono P.μ P.μ_nonneg (fun ω hω => by rw [hω]; exact ha)

/-- **Under the extensional reading, Theorem 3's chain is about junk**: with `αM (ob aₘ)` constant
`aK'` and KDP there, if `ac aₘ ≠ aK'` the fairness cell `(twin aₘ, ac aₘ)` is null and its value
is the junk `0`; so is every cell `(b, ac aₘ)` the chain passes through.
Source: bli-paper-017(a); flags of bli-paper-009, 012, 013
Kind: P
Fidelity: exact
Hyps: (a) the constancy, KDP, `ac aₘ ≠ aK'` -/
theorem kdp_const_fairness_cell_null (S : PaperStructure 𝒟 Act) (L : LimitedSelfMod S)
    (V : ArgmaxVars P) {aₘ aK' : Act} (hM : ∀ ω, V.αM (L.ob aₘ) ω = aK')
    (hK : KnowledgeOfDecisionProcedure V (L.ob aₘ)) (hne : L.ac aₘ ≠ aK') (o : ↥𝒟) :
    (∀ b, P.pairMass o (L.ob aₘ) b (L.ac aₘ) = 0 ∧ cellEU P o (L.ob aₘ) b (L.ac aₘ) = 0) ∧
    P.pairMass o (L.ob aₘ) (S.twin aₘ) (L.ac aₘ) = 0 ∧
    cellEU P o (L.ob aₘ) (S.twin aₘ) (L.ac aₘ) = 0 := by
  have hnull := kdp_const_null V hM hK (L.ac aₘ) hne
  have key : ∀ b, P.pairMass o (L.ob aₘ) b (L.ac aₘ) = 0 ∧ cellEU P o (L.ob aₘ) b (L.ac aₘ) = 0 := by
    intro b
    have hz : P.pairMass o (L.ob aₘ) b (L.ac aₘ) = 0 := by
      apply le_antisymm _ (massOf_nonneg _ P.μ_nonneg _)
      rw [← hnull]
      exact massOf_mono P.μ P.μ_nonneg (fun ω hω => hω.2)
    refine ⟨hz, ?_⟩
    unfold cellEU condExp
    have : massOf P.μ (fun ω => P.pp ω o = b ∧ P.pp ω (L.ob aₘ) = L.ac aₘ) = 0 := hz
    rw [this, div_zero]
  exact ⟨key, (key _).1, (key _).2⟩

/-- **KDP everywhere with constant variables makes `pp` a point mass**: if `αM o = c o` is
constant at every `o` and KDP holds at every `o`, then `μ(pp = c) = 1`, every other policy is
null, and every point `pp · o = a` with `a ≠ c o` is null with junk value `EU o a = 0` — so
"UDT 1.0 strictly prefers `aₘ`" compares junk zeros.
Source: bli-paper-017(a); flags of bli-paper-012, 013
Kind: P
Fidelity: exact
Hyps: (a) the constancies, KDP everywhere -/
theorem kdp_all_const_pointMass (V : ArgmaxVars P) (c : Policy 𝒟 Act)
    (hM : ∀ o ω, V.αM o ω = c o) (hK : ∀ o, KnowledgeOfDecisionProcedure V o) :
    P.policyMass c = 1 ∧ (∀ π, π ≠ c → P.policyMass π = 0) ∧
      ∀ o a, a ≠ c o → P.ppMass o a = 0 ∧ P.EU o a = 0 := by
  have hpt : ∀ o ω, 0 < P.μ ω → P.pp ω o = c o := by
    intro o ω hpos
    have h1 : massOf P.μ (fun ω => P.pp ω o = c o) = 1 := by
      rw [← hK o]
      exact massOf_congr P.μ (fun ω => by rw [hM o ω])
    rw [massOf_eq_one_iff P.μ P.μ_sum_one, massOf_not_eq_zero_iff P.μ P.μ_nonneg] at h1
    exact h1 ω hpos
  have hall : ∀ ω, 0 < P.μ ω → P.pp ω = c := fun ω hpos => funext fun o => hpt o ω hpos
  have hc : P.policyMass c = 1 := by
    unfold FiniteBLIPrior.policyMass
    rw [massOf_eq_one_iff P.μ P.μ_sum_one, massOf_not_eq_zero_iff P.μ P.μ_nonneg]
    exact hall
  refine ⟨hc, fun π hπ => ?_, fun o a ha => ?_⟩
  · unfold FiniteBLIPrior.policyMass
    rw [massOf_eq_zero_iff P.μ P.μ_nonneg]
    intro ω hω
    by_contra hne
    have hpos : 0 < P.μ ω := lt_of_le_of_ne (P.μ_nonneg ω) (Ne.symm hne)
    exact hπ (hω ▸ hall ω hpos)
  · have hz : P.ppMass o a = 0 := by
      unfold FiniteBLIPrior.ppMass
      rw [massOf_eq_zero_iff P.μ P.μ_nonneg]
      intro ω hω
      by_contra hne
      have hpos : 0 < P.μ ω := lt_of_le_of_ne (P.μ_nonneg ω) (Ne.symm hne)
      exact ha (hω ▸ hpt o ω hpos)
    refine ⟨hz, ?_⟩
    unfold FiniteBLIPrior.EU condExp
    have : massOf P.μ (fun ω => P.pp ω o = a) = 0 := hz
    rw [this, div_zero]

end Cleanroom.Udt.UdtPaperTiling
