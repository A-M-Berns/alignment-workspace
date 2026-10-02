import Cleanroom.Udt.UdtPaperTiling.PolicyLevel
import Cleanroom.Bli.UdtBliCore.WitnessCorr

/-!
# `udt-paper-tiling` · PolicyLevelWitness: the policy-level model's witnesses (T12)

All over `twoTables` with `Act = Bool`; `polB a b` is the policy `o ↦ a`, `ō ↦ b`, and
`A = (ff, ff)`, `B = (tt, tt)`, `C = (tt, ff)`.

* `Stoch` (N+ for `policyLevel_tiling`): chosen `A` is modified to `B` with probability `2/3`
  and to `C` with probability `1/3`; `B` and `C` are chosen with mass `1/4` each and never
  modified; `U = 9` on `pp = B`, `6` on `pp = C`. Mean fairness (the utility is a function of the
  effective policy, `meanFair_of_function_of_pp`), Avoidability, a genuinely stochastic kernel,
  and the theorem's inequality strict: `chosenEU A = 8 < 9 = chosenEU B`.
* `NeedAvoid` (2-002(d)): without Avoidability the theorem fails — `A` is modified to `B` (value
  `10`), `C` is chosen and kept (value `0`), and `B` is never chosen: the modifying `A` reaches a
  strictly better effective policy that no non-modifying policy implements.
* `MeanNotCI` (2-003(c)): mean fairness without CI-fairness — a `U` whose variance depends on the
  chosen policy.
* `DistNotMean` (2-003(c)): distributional fairness without mean fairness — kernels all differ, so
  distributional fairness is vacuous, while the cell `(B, A)` has value `10 ≠ 10/3 = effEU A`.
* `TwoStep` (2-004): the two-step kernel `A → B → C`, `C → C`: CI-fair (utility constant),
  **not** Avoidable, and **not** idempotent (`∑ ker A π'' · ker π'' C = 1 ≠ 0 = ker A C`) — the
  inventory's countermodel, which `kerIdempotent_of_avoidable` shows must violate Avoidability.

Package `udt-paper-tiling` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Udt.UdtPaperTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

/-! ## A general lemma: a utility that is a function of the effective policy is mean-fair -/

/-- The conditional expectation of a function constant on a positive event is that constant.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condExp_eq_const_of_eq_on {Ω : Type} [Fintype Ω] (μ f : Ω → ℚ) (E : Ω → Prop)
    [DecidablePred E] (hpos : 0 < massOf μ E) {c : ℚ} (h : ∀ ω, E ω → f ω = c) :
    condExp μ f E = c := by
  unfold condExp
  rw [integralOf_congr_fun μ f (fun _ => c) E h, integralOf_const, mul_div_assoc,
    div_self (ne_of_gt hpos), mul_one]

namespace ModLayer

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {Act : Type} [Fintype Act]
  [DecidableEq Act] {P : FiniteBLIPrior 𝒮 m 𝒟 Act} (M : ModLayer P)

/-- **A utility that depends on the world only through the effective policy is mean-fair.**
Source: none: infrastructure (the witnesses' fairness)
Kind: L
Fidelity: n/a -/
theorem meanFair_of_function_of_pp (c : Policy 𝒟 Act → ℚ) (hU : ∀ ω, P.U ω = c (P.pp ω)) :
    M.MeanFair := by
  intro π π' hpos
  have hpos' : 0 < massOf P.μ (fun ω => P.pp ω = π') :=
    lt_of_lt_of_le hpos (massOf_mono P.μ P.μ_nonneg (fun _ h => h.2))
  unfold cellEU effEU
  rw [condExp_eq_const_of_eq_on P.μ P.U _ hpos (c := c π') (fun ω h => by rw [hU, h.2]),
    condExp_eq_const_of_eq_on P.μ P.U _ hpos' (c := c π') (fun ω h => by rw [hU, h])]

end ModLayer

namespace PLWit

/-- `Rec ≠ Ask`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mRec_ne_mAsk : mRec ≠ mAsk := mAsk_ne_mRec.symm

/-- The two-point Boolean policy. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def polB (a b : Bool) : Policy twoTables Bool := fun T => if T = T1 then a else b

/-- `polB a b o = a`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma polB_T1 (a b : Bool) : polB a b T1 = a := by simp [polB]
/-- `polB a b ō = b`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma polB_T2 (a b : Bool) : polB a b T2 = b := by simp [polB, mRec_ne_mAsk]

/-- `polB` is injective. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma polB_inj {a b a' b' : Bool} : polB a b = polB a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    exact ⟨by simpa using congrFun h T1, by simpa using congrFun h T2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Every policy is a `polB`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma eq_polB (π : Policy twoTables Bool) : π = polB (π T1) (π T2) := by
  funext T
  rcases eq_T1_or_T2 T with rfl | rfl <;> simp

/-- `A = (ff, ff)`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
abbrev A : Policy twoTables Bool := polB false false
/-- `B = (tt, tt)`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
abbrev B : Policy twoTables Bool := polB true true
/-- `C = (tt, ff)`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
abbrev C : Policy twoTables Bool := polB true false

/-! ## `Stoch`: the N+ witness -/

namespace Stoch

/-- The chosen policy by world index: `0, 1 ↦ A`, `2 ↦ B`, `3 ↦ C`.
Source: mandate T12 (N+)
Kind: D
Fidelity: n/a -/
def chosen₀ : Fin 4 → Policy twoTables Bool
  | 0 => A
  | 1 => A
  | 2 => B
  | 3 => C

/-- The effective policy by world index: `0 ↦ B`, `1 ↦ C`, `2 ↦ B`, `3 ↦ C`.
Source: mandate T12 (N+)
Kind: D
Fidelity: n/a -/
def pp₀ : Fin 4 → Policy twoTables Bool
  | 0 => B
  | 1 => C
  | 2 => B
  | 3 => C

/-- The masses: `1/3, 1/6, 1/4, 1/4` (halved over the two states).
Source: mandate T12 (N+)
Kind: D
Fidelity: n/a -/
def w : Fin 4 → ℚ
  | 0 => 1 / 6
  | 1 => 1 / 12
  | 2 => 1 / 8
  | 3 => 1 / 8

/-- The utility as a function of the effective policy: `9` on `B`, `6` on `C`, `0` otherwise.
Source: mandate T12 (N+)
Kind: D
Fidelity: n/a -/
def c (π : Policy twoTables Bool) : ℚ := if π = B then 9 else if π = C then 6 else 0

/-- **The N+ prior.** Source: mandate T12. Kind: D. Fidelity: n/a -/
def prior : FiniteBLIPrior witIndex 1 twoTables Bool :=
  handPrior (Fin 2 × Fin 4) (fun ω => w ω.2) (fun ω => by
      rcases ω with ⟨_, i⟩; match i with | 0 | 1 | 2 | 3 => norm_num [w])
    (by simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four]; norm_num [w])
    (fun ω => twoState ω.1) two_zeroOne (fun ω => pp₀ ω.2) (fun ω => c (pp₀ ω.2))

/-- The modification layer. Source: mandate T12. Kind: D. Fidelity: n/a -/
def M : ModLayer prior where
  chosen := fun ω => chosen₀ ω.2

/-- `polB`-equations the simplifier needs. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma AB : A ≠ B := by simp [polB_inj]
/-- `A ≠ C`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma AC : A ≠ C := by simp [polB_inj]
/-- `B ≠ C`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma BC : B ≠ C := by simp [polB_inj]

/-- **Mean fairness holds** (the utility is a function of the effective policy).
Source: mandate T12
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem meanFair : M.MeanFair := M.meanFair_of_function_of_pp c (fun _ => rfl)

/-- The masses of the chosen policies. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma chosenMass_eq : M.chosenMass A = 1 / 2 ∧ M.chosenMass B = 1 / 4 ∧ M.chosenMass C = 1 / 4 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · unfold ModLayer.chosenMass prior
    rw [handPrior_massOf]
    simp only [polB_inj, handPrior, massOf, M, chosen₀, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_four, w, AB, AC, BC, AB.symm, AC.symm, BC.symm]
    norm_num [polB_inj, A, B, C]

/-- The kernel of `A` is genuinely stochastic: `ker A B = 2/3`, `ker A C = 1/3`.
Source: mandate T12 (N+: "a policy that is modified with probability 1/3")
Kind: L
Fidelity: n/a -/
lemma ker_A : M.ker A B = 2 / 3 ∧ M.ker A C = 1 / 3 := by
  obtain ⟨hA, _, _⟩ := chosenMass_eq
  refine ⟨?_, ?_⟩ <;>
  · unfold ModLayer.ker
    rw [hA]
    unfold ModLayer.cellMass prior
    rw [handPrior_massOf]
    simp only [polB_inj, handPrior, massOf, M, chosen₀, pp₀, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_four, w, AB, AC, BC, AB.symm, AC.symm, BC.symm]
    norm_num [polB_inj, A, B, C]

/-- The reachable policies are `B` and `C`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma reachable_cases {π : Policy twoTables Bool} (h : M.Reachable π) : π = B ∨ π = C := by
  obtain ⟨π', hπ'⟩ := h
  obtain ⟨ω, ⟨_, hp⟩, _⟩ := (massOf_pos_iff prior.μ prior.μ_nonneg _).mp hπ'
  rw [← hp]
  rcases ω with ⟨_, i⟩
  match i with
  | 0 => simp [prior, handPrior, pp₀]
  | 1 => simp [prior, handPrior, pp₀]
  | 2 => simp [prior, handPrior, pp₀]
  | 3 => simp [prior, handPrior, pp₀]

/-- `B` and `C` are never modified. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma not_modifying_BC : ¬ M.Modifying B ∧ ¬ M.Modifying C := by
  constructor <;>
  · rw [ModLayer.not_modifying_iff]
    unfold prior
    rw [handPrior_massOf]
    simp only [polB_inj, handPrior, massOf, M, chosen₀, pp₀, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_four, w, AB, AC, BC, AB.symm, AC.symm, BC.symm]
    norm_num [polB_inj, A, B, C]

/-- **Avoidability holds**: every reachable policy (`B`, `C`) is positively chosen and
non-modifying.
Source: mandate T12
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem avoidable : M.Avoidable := by
  rw [ModLayer.avoidable_iff]
  intro π hr
  obtain ⟨_, hB, hC⟩ := chosenMass_eq
  obtain ⟨nB, nC⟩ := not_modifying_BC
  rcases reachable_cases hr with rfl | rfl
  · exact ⟨by rw [hB]; norm_num, nB⟩
  · exact ⟨by rw [hC]; norm_num, nC⟩

/-- `A` is modifying. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma modifying_A : M.Modifying A := by
  unfold ModLayer.Modifying prior
  rw [handPrior_massOf]
  simp only [polB_inj, handPrior, massOf, M, chosen₀, pp₀, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fin.sum_univ_four, w, AB, AC, BC, AB.symm, AC.symm, BC.symm]
  norm_num [polB_inj, A, B, C]

/-- The values: `chosenEU A = 8`, `chosenEU B = 9`. Source: mandate T12. Kind: L. Fidelity: n/a -/
lemma chosenEU_eq : M.chosenEU A = 8 ∧ M.chosenEU B = 9 := by
  refine ⟨?_, ?_⟩ <;>
  · unfold ModLayer.chosenEU prior
    rw [handPrior_condExp]
    simp only [polB_inj, handPrior, condExp, massOf, integralOf, M, chosen₀, pp₀, c, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_four, w, AB, AC, BC, AB.symm, AC.symm, BC.symm]
    norm_num [polB_inj, A, B, C]

/-- **The N+ witness of the policy-level tiling theorem**: mean fairness, Avoidability, a
modifying chosen policy `A` with a genuinely stochastic kernel (`2/3`, `1/3`), and the theorem's
inequality strict for it: `chosenEU A = 8 < 9 = chosenEU B` with `B` non-modifying and positive.
Source: mandate T12 (N+)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem grade_Nplus :
    M.MeanFair ∧ M.Avoidable ∧ M.Modifying A ∧ M.ker A B = 2 / 3 ∧ M.ker A C = 1 / 3 ∧
    ¬ M.Modifying B ∧ 0 < M.chosenMass B ∧ M.chosenEU A < M.chosenEU B := by
  obtain ⟨_, hB, _⟩ := chosenMass_eq
  obtain ⟨kB, kC⟩ := ker_A
  obtain ⟨vA, vB⟩ := chosenEU_eq
  exact ⟨meanFair, avoidable, modifying_A, kB, kC, not_modifying_BC.1, by rw [hB]; norm_num,
    by rw [vA, vB]; norm_num⟩

end Stoch

/-! ## `NeedAvoid`: without Avoidability the theorem fails -/

namespace NeedAvoid

/-- The chosen policy by index: `0 ↦ A`, `1 ↦ C`. Source: bli-paper-2-002(d). Kind: D. Fidelity: n/a -/
def chosen₀ : Fin 2 → Policy twoTables Bool
  | 0 => A
  | 1 => C

/-- The effective policy by index: `0 ↦ B`, `1 ↦ C`. Source: bli-paper-2-002(d). Kind: D. Fidelity: n/a -/
def pp₀ : Fin 2 → Policy twoTables Bool
  | 0 => B
  | 1 => C

/-- The utility: `10` on `pp = B`, `0` otherwise. Source: bli-paper-2-002(d). Kind: D. Fidelity: n/a -/
def c (π : Policy twoTables Bool) : ℚ := if π = B then 10 else 0

/-- **The countermodel for Avoidability.** Source: bli-paper-2-002(d). Kind: D. Fidelity: n/a -/
def prior : FiniteBLIPrior witIndex 1 twoTables Bool :=
  handPrior (Fin 2 × Fin 2) (fun _ => 1 / 4) (fun _ => by norm_num)
    (by norm_num [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin])
    (fun ω => twoState ω.1) two_zeroOne (fun ω => pp₀ ω.2) (fun ω => c (pp₀ ω.2))

/-- The modification layer. Source: bli-paper-2-002(d). Kind: D. Fidelity: n/a -/
def M : ModLayer prior where
  chosen := fun ω => chosen₀ ω.2

/-- The positive chosen policies are `A` and `C`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pos_cases {π : Policy twoTables Bool} (h : 0 < M.chosenMass π) : π = A ∨ π = C := by
  obtain ⟨ω, hω, _⟩ := (massOf_pos_iff prior.μ prior.μ_nonneg _).mp h
  rw [← hω]
  rcases ω with ⟨_, i⟩
  match i with
  | 0 => simp [M, chosen₀]
  | 1 => simp [M, chosen₀]

/-- `A` is modifying and `B` is never chosen. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma facts : M.Modifying A ∧ M.chosenMass B = 0 ∧ M.chosenMass A = 1 / 2 ∧
    M.chosenEU A = 10 ∧ M.chosenEU C = 0 ∧ M.Reachable B := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨A, ?_⟩⟩ <;>
  · first
    | unfold ModLayer.Modifying prior
    | unfold ModLayer.chosenMass prior
    | unfold ModLayer.chosenEU prior
    | unfold ModLayer.cellMass prior
    first | rw [handPrior_massOf] | rw [handPrior_condExp]
    simp only [polB_inj, handPrior, condExp, massOf, integralOf, M, chosen₀, pp₀, c, Fintype.sum_prod_type,
      Fin.sum_univ_two, Stoch.AB, Stoch.AC, Stoch.BC, Stoch.AB.symm, Stoch.AC.symm, Stoch.BC.symm]
    norm_num [polB_inj, A, B, C]

/-- **Avoidability is needed** (bli-paper-2-002(d)): mean fairness holds, `A` is modifying and
reaches `B` (value `10`), no non-modifying positive policy implements `B` (so Avoidability fails),
and the theorem's conclusion is false for `A`: the only non-modifying positive policy is `C`,
with value `0 < 10`.
Source: bli-paper-2-002(b),(d); l5 b.175 ("Otherwise, there can be an incentive to choose a
modifying policy")
Kind: N−
Fidelity: n/a (refutation of the theorem without Avoidability)
Hyps: (a) none -/
theorem avoidability_needed :
    M.MeanFair ∧ ¬ M.Avoidable ∧
    ¬ ∃ π, ¬ M.Modifying π ∧ 0 < M.chosenMass π ∧ M.chosenEU A ≤ M.chosenEU π := by
  obtain ⟨mA, mB, mA', vA, vC, rB⟩ := facts
  refine ⟨M.meanFair_of_function_of_pp c (fun _ => rfl), fun hA => ?_, ?_⟩
  · have := ((M.avoidable_iff.mp hA) B rB).1
    rw [mB] at this
    exact lt_irrefl _ this
  · rintro ⟨π, hnm, hpos, hle⟩
    rcases pos_cases hpos with rfl | rfl
    · exact hnm mA
    · rw [vA, vC] at hle; norm_num at hle

end NeedAvoid

/-! ## `MeanNotCI`: mean fairness without CI-fairness -/

namespace MeanNotCI

/-- Worlds: `(A, B, U = 0)`, `(A, B, U = 20)`, `(B, B, U = 10)` with masses `1/4, 1/4, 1/2`.
Source: bli-paper-2-003(c)
Kind: D
Fidelity: n/a -/
def chosen₀ : Fin 3 → Policy twoTables Bool
  | 0 => A
  | 1 => A
  | 2 => B

/-- The utility by index. Source: bli-paper-2-003(c). Kind: D. Fidelity: n/a -/
def u : Fin 3 → ℚ
  | 0 => 0
  | 1 => 20
  | 2 => 10

/-- The masses by index (halved over the two states). Source: bli-paper-2-003(c). Kind: D. Fidelity: n/a -/
def w : Fin 3 → ℚ
  | 0 => 1 / 8
  | 1 => 1 / 8
  | 2 => 1 / 4

/-- The prior: every world has effective policy `B`. Source: bli-paper-2-003(c). Kind: D. Fidelity: n/a -/
def prior : FiniteBLIPrior witIndex 1 twoTables Bool :=
  handPrior (Fin 2 × Fin 3) (fun ω => w ω.2) (fun ω => by
      rcases ω with ⟨_, i⟩; match i with | 0 | 1 | 2 => norm_num [w])
    (by simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]; norm_num [w])
    (fun ω => twoState ω.1) two_zeroOne (fun _ => B) (fun ω => u ω.2)

/-- The modification layer. Source: bli-paper-2-003(c). Kind: D. Fidelity: n/a -/
def M : ModLayer prior where
  chosen := fun ω => chosen₀ ω.2

/-- A positive cell has `π' = B` and `π ∈ {A, B}`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cell_cases {π π' : Policy twoTables Bool} (h : 0 < M.cellMass π π') :
    π' = B ∧ (π = A ∨ π = B) := by
  obtain ⟨ω, ⟨hc, hp⟩, _⟩ := (massOf_pos_iff prior.μ prior.μ_nonneg _).mp h
  refine ⟨hp.symm, ?_⟩
  rw [← hc]
  rcases ω with ⟨_, i⟩
  match i with
  | 0 => simp [M, chosen₀]
  | 1 => simp [M, chosen₀]
  | 2 => simp [M, chosen₀]

/-- The cell and effective values are all `10`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma values : M.cellEU A B = 10 ∧ M.cellEU B B = 10 ∧ M.effEU B = 10 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · first | unfold ModLayer.cellEU prior | unfold ModLayer.effEU prior
    rw [handPrior_condExp]
    simp only [polB_inj, handPrior, condExp, massOf, integralOf, M, chosen₀, u, w, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three, Stoch.AB, Stoch.AB.symm]
    norm_num [polB_inj, A, B, C]

/-- **Mean fairness holds but CI-fairness fails**: both positive cells have mean `10 = effEU B`,
while at `u = 20` the product form gives `1/4 · 1 ≠ 1/4 · 1/2`.
Source: bli-paper-2-003(c)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem meanFair_not_ciFair : M.MeanFair ∧ ¬ M.CIFair := by
  obtain ⟨vAB, vBB, vB⟩ := values
  constructor
  · intro π π' hpos
    obtain ⟨rfl, hπ⟩ := cell_cases hpos
    rcases hπ with rfl | rfl
    · rw [vAB, vB]
    · rw [vBB, vB]
  · intro h
    have := h A B 20
    unfold ModLayer.cellMass prior at this
    rw [handPrior_massOf, handPrior_massOf, handPrior_massOf, handPrior_massOf] at this
    simp only [polB_inj, handPrior, massOf, M, chosen₀, u, w, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three, Stoch.AB, Stoch.AB.symm] at this
    norm_num at this

end MeanNotCI

/-! ## `DistNotMean`: distributional fairness without mean fairness -/

namespace DistNotMean

/-- Worlds: `(A, A, 0)` mass `1/2`, `(B, A, 10)` mass `1/4`, `(B, B, 10)` mass `1/4`.
Source: bli-paper-2-003(c)
Kind: D
Fidelity: n/a -/
def chosen₀ : Fin 3 → Policy twoTables Bool
  | 0 => A
  | 1 => B
  | 2 => B

/-- The effective policy by index. Source: bli-paper-2-003(c). Kind: D. Fidelity: n/a -/
def pp₀ : Fin 3 → Policy twoTables Bool
  | 0 => A
  | 1 => A
  | 2 => B

/-- The utility by index. Source: bli-paper-2-003(c). Kind: D. Fidelity: n/a -/
def u : Fin 3 → ℚ
  | 0 => 0
  | 1 => 10
  | 2 => 10

/-- The masses by index (halved). Source: bli-paper-2-003(c). Kind: D. Fidelity: n/a -/
def w : Fin 3 → ℚ
  | 0 => 1 / 4
  | 1 => 1 / 8
  | 2 => 1 / 8

/-- The prior. Source: bli-paper-2-003(c). Kind: D. Fidelity: n/a -/
def prior : FiniteBLIPrior witIndex 1 twoTables Bool :=
  handPrior (Fin 2 × Fin 3) (fun ω => w ω.2) (fun ω => by
      rcases ω with ⟨_, i⟩; match i with | 0 | 1 | 2 => norm_num [w])
    (by simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]; norm_num [w])
    (fun ω => twoState ω.1) two_zeroOne (fun ω => pp₀ ω.2) (fun ω => u ω.2)

/-- The modification layer. Source: bli-paper-2-003(c). Kind: D. Fidelity: n/a -/
def M : ModLayer prior where
  chosen := fun ω => chosen₀ ω.2

/-- The positive chosen policies are `A` and `B`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pos_cases {π : Policy twoTables Bool} (h : 0 < M.chosenMass π) : π = A ∨ π = B := by
  obtain ⟨ω, hω, _⟩ := (massOf_pos_iff prior.μ prior.μ_nonneg _).mp h
  rw [← hω]
  rcases ω with ⟨_, i⟩
  match i with
  | 0 => simp [M, chosen₀]
  | 1 => simp [M, chosen₀]
  | 2 => simp [M, chosen₀]

/-- The kernels differ (`ker A B = 0 ≠ 1/2 = ker B B`), the cell `(B, A)` is positive with value
`10`, and `effEU A = 10/3`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma facts : M.ker A B = 0 ∧ M.ker B B = 1 / 2 ∧ 0 < M.cellMass B A ∧ M.cellEU B A = 10 ∧
    M.effEU A = 10 / 3 := by
  have hA : M.chosenMass A = 1 / 2 := by
    unfold ModLayer.chosenMass prior
    rw [handPrior_massOf]
    simp only [polB_inj, handPrior, massOf, M, chosen₀, w, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three, Stoch.AB, Stoch.AB.symm]
    norm_num [polB_inj, A, B, C]
  have hB : M.chosenMass B = 1 / 2 := by
    unfold ModLayer.chosenMass prior
    rw [handPrior_massOf]
    simp only [polB_inj, handPrior, massOf, M, chosen₀, w, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three, Stoch.AB, Stoch.AB.symm]
    norm_num [polB_inj, A, B, C]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold ModLayer.ker; rw [hA]
    unfold ModLayer.cellMass prior
    rw [handPrior_massOf]
    simp only [polB_inj, handPrior, massOf, M, chosen₀, pp₀, w, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three, Stoch.AB, Stoch.AB.symm]
    norm_num [polB_inj, A, B, C]
  · unfold ModLayer.ker; rw [hB]
    unfold ModLayer.cellMass prior
    rw [handPrior_massOf]
    simp only [polB_inj, handPrior, massOf, M, chosen₀, pp₀, w, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three, Stoch.AB, Stoch.AB.symm]
    norm_num [polB_inj, A, B, C]
  · unfold ModLayer.cellMass prior
    rw [handPrior_massOf]
    simp only [polB_inj, handPrior, massOf, M, chosen₀, pp₀, w, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three, Stoch.AB, Stoch.AB.symm]
    norm_num [polB_inj, A, B, C]
  · unfold ModLayer.cellEU prior
    rw [handPrior_condExp]
    simp only [polB_inj, handPrior, condExp, massOf, integralOf, M, chosen₀, pp₀, u, w,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, Stoch.AB, Stoch.AB.symm]
    norm_num [polB_inj, A, B, C]
  · unfold ModLayer.effEU prior
    rw [handPrior_condExp]
    simp only [polB_inj, handPrior, condExp, massOf, integralOf, pp₀, u, w, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three, Stoch.AB, Stoch.AB.symm]
    norm_num [polB_inj, A, B, C]

/-- **Distributional fairness holds but mean fairness fails**: the two positive chosen policies
have different kernels, so distributional fairness is vacuous, while the cell `(B, A)` has value
`10 ≠ 10/3 = effEU A` — the utility depends on the chosen policy beyond the effective one,
invisibly to kernel comparisons.
Source: bli-paper-2-003(c)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem distFair_not_meanFair : M.DistFair ∧ ¬ M.MeanFair := by
  obtain ⟨kAB, kBB, hBA, vBA, vA⟩ := facts
  constructor
  · intro π₁ π₂ hker h₁ h₂
    rcases pos_cases h₁ with rfl | rfl <;> rcases pos_cases h₂ with rfl | rfl
    · rfl
    · have := hker B; rw [kAB, kBB] at this; norm_num at this
    · have := hker B; rw [kAB, kBB] at this; norm_num at this
    · rfl
  · intro h
    have := h B A hBA
    rw [vBA, vA] at this
    norm_num at this

end DistNotMean

/-! ## `TwoStep`: the two-step kernel is CI-fair, not Avoidable, not idempotent -/

namespace TwoStep

/-- Worlds: `(A, B)`, `(B, C)`, `(C, C)`, mass `1/3` each. Source: bli-paper-2-004. Kind: D. Fidelity: n/a -/
def chosen₀ : Fin 3 → Policy twoTables Bool
  | 0 => A
  | 1 => B
  | 2 => C

/-- The effective policy by index. Source: bli-paper-2-004. Kind: D. Fidelity: n/a -/
def pp₀ : Fin 3 → Policy twoTables Bool
  | 0 => B
  | 1 => C
  | 2 => C

/-- The prior (utility constantly `0`). Source: bli-paper-2-004. Kind: D. Fidelity: n/a -/
def prior : FiniteBLIPrior witIndex 1 twoTables Bool :=
  handPrior (Fin 2 × Fin 3) (fun _ => 1 / 6) (fun _ => by norm_num)
    (by norm_num [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin])
    (fun ω => twoState ω.1) two_zeroOne (fun ω => pp₀ ω.2) (fun _ => 0)

/-- The modification layer. Source: bli-paper-2-004. Kind: D. Fidelity: n/a -/
def M : ModLayer prior where
  chosen := fun ω => chosen₀ ω.2

/-- **A constant utility is CI-fair** (both sides of the product form agree).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ciFair : M.CIFair := by
  intro π π' u
  show massOf prior.μ (fun ω => (0 : ℚ) = u ∧ M.chosen ω = π ∧ prior.pp ω = π') * _ =
    massOf prior.μ (fun ω => (0 : ℚ) = u ∧ prior.pp ω = π') * _
  by_cases hu : (0 : ℚ) = u
  · simp only [hu, true_and]
    unfold ModLayer.cellMass
    ring
  · simp only [hu, false_and]
    unfold massOf
    simp

/-- The kernel entries. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma kers : M.ker A B = 1 ∧ M.ker B C = 1 ∧ M.ker A C = 0 ∧ M.ker A A = 0 ∧ M.ker C C = 1 := by
  have hA : M.chosenMass A = 1 / 3 := by
    unfold ModLayer.chosenMass prior
    rw [handPrior_massOf]
    simp only [polB_inj, handPrior, massOf, M, chosen₀, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three, Stoch.AB, Stoch.AC, Stoch.BC, Stoch.AB.symm, Stoch.AC.symm, Stoch.BC.symm]
    norm_num [polB_inj, A, B, C]
  have hB : M.chosenMass B = 1 / 3 := by
    unfold ModLayer.chosenMass prior
    rw [handPrior_massOf]
    simp only [polB_inj, handPrior, massOf, M, chosen₀, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three, Stoch.AB, Stoch.AC, Stoch.BC, Stoch.AB.symm, Stoch.AC.symm, Stoch.BC.symm]
    norm_num [polB_inj, A, B, C]
  have hC : M.chosenMass C = 1 / 3 := by
    unfold ModLayer.chosenMass prior
    rw [handPrior_massOf]
    simp only [polB_inj, handPrior, massOf, M, chosen₀, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three, Stoch.AB, Stoch.AC, Stoch.BC, Stoch.AB.symm, Stoch.AC.symm, Stoch.BC.symm]
    norm_num [polB_inj, A, B, C]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · unfold ModLayer.ker
    first | rw [hA] | rw [hB] | rw [hC]
    unfold ModLayer.cellMass prior
    rw [handPrior_massOf]
    simp only [polB_inj, handPrior, massOf, M, chosen₀, pp₀, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three, Stoch.AB, Stoch.AC, Stoch.BC, Stoch.AB.symm, Stoch.AC.symm, Stoch.BC.symm]
    norm_num [polB_inj, A, B, C]

/-- Every kernel entry out of `A` other than `B` vanishes. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma ker_A_other (π : Policy twoTables Bool) (hπ : π ≠ B) : M.ker A π = 0 := by
  apply M.ker_eq_zero_of_cellMass_eq_zero
  unfold ModLayer.cellMass
  rw [massOf_eq_zero_iff prior.μ prior.μ_nonneg]
  rintro ⟨_, i⟩ ⟨hc, hp⟩
  exfalso
  match i with
  | 0 => exact hπ (by simpa [prior, handPrior, pp₀] using hp.symm)
  | 1 => exact Stoch.AB (by simpa [M, chosen₀] using hc.symm)
  | 2 => exact Stoch.AC (by simpa [M, chosen₀] using hc.symm)

/-- **The two-step kernel**: CI-fair, not Avoidable (`B` is reachable yet modifying), and not
idempotent — `∑_{π''} ker A π'' · ker π'' C = ker A B · ker B C = 1 ≠ 0 = ker A C`. By
`kerIdempotent_of_avoidable`, any such countermodel must fail Avoidability.
Source: bli-paper-2-004 (both readings; the inventory's "two-step modification")
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem twoStep : M.CIFair ∧ ¬ M.Avoidable ∧ ¬ M.KerIdempotent := by
  obtain ⟨kAB, kBC, kAC, kAA, kCC⟩ := kers
  refine ⟨ciFair, fun hA => ?_, fun hI => ?_⟩
  · have hr : M.Reachable B := ⟨A, M.cellMass_pos_of_ker_pos (by rw [kAB]; norm_num)⟩
    have hnm := ((M.avoidable_iff.mp hA) B hr).2
    rw [ModLayer.not_modifying_iff] at hnm
    have : M.cellMass B C = 0 := by
      apply le_antisymm _ (massOf_nonneg _ prior.μ_nonneg _)
      rw [← hnm]
      exact massOf_mono prior.μ prior.μ_nonneg (fun ω h => ⟨h.1, fun hb => Stoch.BC (hb.symm.trans h.2)⟩)
    have := M.ker_eq_zero_of_cellMass_eq_zero this
    rw [kBC] at this
    exact one_ne_zero this
  · have := hI A C
    rw [Finset.sum_eq_single B] at this
    · rw [kAB, kBC, kAC] at this; norm_num at this
    · intro π _ hπ
      rw [ker_A_other π hπ, zero_mul]
    · intro h; exact absurd (Finset.mem_univ B) h

end TwoStep

end PLWit

end Cleanroom.Udt.UdtPaperTiling
