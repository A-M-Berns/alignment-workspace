import Cleanroom.Udt.UdtPaperTiling.Coordination
import Cleanroom.Udt.UdtPaperTiling.Vingean
import Cleanroom.Udt.UdtPaperTiling.Tables

/-!
# `udt-paper-tiling` · IncomparableWitness: Policy Coordination and (extensional) Naive Action
Coordination are incomparable (T8(b), bli-paper-018)

**The extensional form of Naive Action Coordination** (`NaiveActionCoordinationExt`): the
*set* of maximizers of `a ↦ 𝔼[U | π*(o₁) = a ∧ π*(o₂) = a₁]` over positive cells equals the set of
maximizers of `a ↦ 𝔼[U | π*(o₁) = a]` over positive points — the paper's "the argmax … = the
argmax …" with probability one, read with every argmax evaluated at the meta level, and with ties
handled as sets. (`Collapse.lean`'s `naiveActionCoordination_const_iff` is the single-constant
version.)

* **PC ∧ ¬NAC** (`CB`): Coordinated Buttons (`udt-policy-calc`'s `coordButtons`: 10/5/0) on the
  trivial layer with independent points and `P(green) = 3/5`. The marginal argmax at `o₁` is
  green (`6 > 2`); conditional on `o₂ = red` it is red (`5 > 0`); so the extensional NAC fails at
  `(o₁, o₂, red)`. The only policy at least as good as `πstar = (green, green)` is itself, so
  Policy Coordination holds.
* **NAC ∧ ¬PC** (`Three`): three observations, `Act = Bool`, independent uniform points, and the
  symmetric utility `U(aaa) = 9`, one `b` ↦ `10`, two `b`s ↦ `0`, `U(bbb) = 9`. At every pair
  `(o₁, o₂)` and every conditioning action the conditional maximizer is `a` and so is the
  marginal one (`29/4 > 19/4`), so extensional NAC holds everywhere with unique maximizers; yet
  `aab` is better than `aaa` overall (`10 > 9`) while its point at `o₃` is worse
  (`19/4 < 29/4`), so Policy Coordination fails. **Finding** (against the mandate's expectation
  that "ties or correlation" would be needed): neither is — a *third* observation is what NAC's
  one-other-point conditioning cannot see; with two observations and unique maximizers NAC implies
  PC (the pairwise-best cell is the global optimum).

Package `udt-paper-tiling` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Udt.UdtPaperTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {Act : Type} [Fintype Act]
  [DecidableEq Act] (P : FiniteBLIPrior 𝒮 m 𝒟 Act)

/-- A meta-level marginal maximizer at `o` (over positive points).
Source: `main.tex` 372–376 read extensionally (bli-paper-015, 017(a))
Kind: D
Fidelity: exact (positive points only) -/
def IsMargArgmax (o : ↥𝒟) (a : Act) : Prop :=
  0 < P.ppMass o a ∧ ∀ b, 0 < P.ppMass o b → P.EU o b ≤ P.EU o a

/-- A meta-level conditional maximizer at `o₁` given `π*(o₂) = a₁` (over positive cells).
Source: `main.tex` 372–376 read extensionally (bli-paper-015, 017(a))
Kind: D
Fidelity: exact (positive cells only) -/
def IsCondArgmax (o₁ o₂ : ↥𝒟) (a₁ a : Act) : Prop :=
  0 < P.pairMass o₁ o₂ a a₁ ∧
  ∀ b, 0 < P.pairMass o₁ o₂ b a₁ → cellEU P o₁ o₂ b a₁ ≤ cellEU P o₁ o₂ a a₁

/-- **Naive Action Coordination, extensional form** at `(o₁, o₂, a₁)`: for non-modifying `a₁`, the
conditional and marginal maximizer sets coincide.
Source: `main.tex` 372–376 (bli-paper-015), extensional reading with ties as sets (mandate T8(b))
Kind: D
Fidelity: variant: maximizer sets in place of "the argmax" -/
def NaiveActionCoordinationExt (S : PaperStructure 𝒟 Act) (o₁ o₂ : ↥𝒟) (a₁ : Act) : Prop :=
  a₁ ∉ S.selfMod → ∀ a, IsCondArgmax P o₁ o₂ a₁ a ↔ IsMargArgmax P o₁ a

/-- A structure with no self-modification: every action available everywhere.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def PaperStructure.plain (𝒟 : Finset (Table 𝒮 m)) (Act : Type) [Fintype Act] [DecidableEq Act] :
    PaperStructure 𝒟 Act where
  Aof := fun _ => Finset.univ
  selfMod := ∅
  twin := id
  twin_nonMod := fun _ => Finset.notMem_empty _
  twin_typed := fun _ _ _ => Finset.mem_univ _
  twin_id := fun _ _ => rfl
  mod := fun _ _ => none
  mod_nonMod_none := fun _ _ _ => rfl

/-! ## PC ∧ ¬NAC: Coordinated Buttons with `P(green) = 3/5` -/

namespace CB

/-- `Rec ≠ Ask`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mRec_ne_mAsk : mRec ≠ mAsk := mAsk_ne_mRec.symm

/-- The weight of a point: `3/5` for green (`true`), `2/5` for red. Source: bli-paper-018. Kind: D. Fidelity: n/a -/
def wt (b : Bool) : ℚ := if b then 3 / 5 else 2 / 5

/-- The product weight, halved over the two states. Source: bli-paper-018. Kind: D. Fidelity: n/a -/
def w (ω : Fin 2 × Bool × Bool) : ℚ := (1 / 2) * (wt ω.2.1 * wt ω.2.2)

/-- The policy points. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def pp₀ (ω : Fin 2 × Bool × Bool) : Policy twoTables Bool := fun T => if T = T1 then ω.2.1 else ω.2.2

/-- Coordinated Buttons: both green ↦ 10, both red ↦ 5, else 0.
Source: `main.tex` 129–133; `udt-policy-calc` `coordButtons`
Kind: D
Fidelity: exact -/
def U₀ (ω : Fin 2 × Bool × Bool) : ℚ :=
  if ω.2.1 ∧ ω.2.2 then 10 else if ¬ ω.2.1 ∧ ¬ ω.2.2 then 5 else 0

/-- **The prior**: independent points with `P(green) = 3/5`. Source: bli-paper-018. Kind: D. Fidelity: n/a -/
def prior : FiniteBLIPrior witIndex 1 twoTables Bool :=
  handPrior (Fin 2 × Bool × Bool) w
    (fun ω => by rcases ω with ⟨_, b₁, b₂⟩; cases b₁ <;> cases b₂ <;> norm_num [w, wt])
    (by simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]; norm_num [w, wt])
    (fun ω => twoState ω.1) two_zeroOne pp₀ U₀

/-- The trivial paper layer. Source: mandate T8(b). Kind: D. Fidelity: n/a -/
def Λ : PaperLayer prior := PaperLayer.trivial prior

/-- The structure (no self-modification). Source: mandate T8(b). Kind: D. Fidelity: n/a -/
def S : PaperStructure twoTables Bool := PaperStructure.plain twoTables Bool

/-- A policy on `twoTables` as a pair. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def pol (a b : Bool) : Policy twoTables Bool := fun T => if T = T1 then a else b

/-- Every policy is a `pol`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma eq_pol (π : Policy twoTables Bool) : π = pol (π T1) (π T2) := by
  funext T
  rcases eq_T1_or_T2 T with rfl | rfl <;> simp [pol, mRec_ne_mAsk]

/-- The event `pp = pol a b`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pp_eq_pol (ω : Fin 2 × Bool × Bool) (a b : Bool) : pp₀ ω = pol a b ↔ ω.2.1 = a ∧ ω.2.2 = b := by
  constructor
  · intro h
    exact ⟨by simpa [pp₀, pol] using congrFun h T1, by simpa [pp₀, pol, mRec_ne_mAsk] using congrFun h T2⟩
  · rintro ⟨h₁, h₂⟩
    funext T
    rcases eq_T1_or_T2 T with rfl | rfl <;> simp [pp₀, pol, mRec_ne_mAsk, h₁, h₂]

/-- The ex-ante values of the four policies. Source: bli-paper-018. Kind: L. Fidelity: n/a -/
lemma procEU_eq : Λ.procEU (pol true true) = 10 ∧ Λ.procEU (pol false false) = 5 ∧
    Λ.procEU (pol true false) = 0 ∧ Λ.procEU (pol false true) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [PaperLayer.procEU_eq]
    show condExp prior.μ prior.U (fun ω => prior.pp ω = _) = _
    unfold prior
    rw [handPrior_condExp]
    simp only [handPrior, condExp, massOf, integralOf, pp_eq_pol, U₀, w, wt,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
    norm_num

/-- The marginal values at `o₁`: green `6`, red `2`; the conditional values at `o₁` given
`o₂ = red`: red `5`, green `0`; and the positivity of the cells and points.
Source: bli-paper-018 (the inventory's numbers)
Kind: L
Fidelity: n/a -/
lemma numbers : prior.EU T1 true = 6 ∧ prior.EU T1 false = 2 ∧
    cellEU prior T1 T2 false false = 5 ∧ cellEU prior T1 T2 true false = 0 ∧
    0 < prior.pairMass T1 T2 false false ∧ 0 < prior.pairMass T1 T2 true false ∧
    0 < prior.ppMass T1 true ∧ 0 < prior.ppMass T1 false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · first
    | unfold FiniteBLIPrior.EU prior
    | unfold cellEU prior
    | unfold FiniteBLIPrior.pairMass prior
    | unfold FiniteBLIPrior.ppMass prior
    first | rw [handPrior_condExp] | rw [handPrior_massOf]
    simp only [handPrior, condExp, massOf, integralOf, pp₀, U₀, w, wt, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fintype.sum_bool]
    simp [mRec_ne_mAsk]
    try norm_num

/-- **Policy Coordination holds** for `πstar = (green, green)`: no other policy is as good, so PC
fires only reflexively — N− (audit r1; the mandate's "N+ for models with all policies positive"
convention is not [[STANDARDS]] §3's). A model where PC fires at a policy other than `πstar` is
`Thm2Wit.pc_fires` (`Theorem2Witness.lean`).
Source: bli-paper-018
Kind: N−
Fidelity: n/a (PC holds vacuously beyond `πstar` itself: the inventory's model)
Hyps: (a) none -/
theorem pc : PolicyCoordination S Λ (pol true true) := by
  intro π _ _ hle o _ _
  obtain ⟨v11, v00, v10, v01⟩ := procEU_eq
  have hπ := eq_pol π
  rw [hπ] at hle ⊢
  cases h1 : π T1 <;> cases h2 : π T2 <;> simp only [h1, h2] at hle ⊢
  · rw [v11, v00] at hle; norm_num at hle
  · rw [v11, v01] at hle; norm_num at hle
  · rw [v11, v10] at hle; norm_num at hle
  · exact le_refl _

/-- **Extensional Naive Action Coordination fails** at `(o₁, o₂, red)`: red is the conditional
maximizer at `o₁` given `o₂ = red` (`5 > 0`), but not the marginal one (`2 < 6`).
Source: bli-paper-018
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem not_nac : ¬ NaiveActionCoordinationExt prior S T1 T2 false := by
  intro h
  obtain ⟨e1, e0, c0, c1, p00, p10, q1, q0⟩ := numbers
  have hcond : IsCondArgmax prior T1 T2 false false := by
    refine ⟨p00, fun b _ => ?_⟩
    cases b
    · exact le_refl _
    · rw [c1, c0]; norm_num
  have := (h (Finset.notMem_empty _) false).mp hcond
  have h2 := this.2 true q1
  rw [e1, e0] at h2
  norm_num at h2

/-- **PC ⇏ NAC**: on Coordinated Buttons with `P(green) = 3/5`, Policy Coordination holds and the
extensional Naive Action Coordination fails.
Source: bli-paper-018
Kind: P
Fidelity: exact (finite model)
Hyps: (a) none -/
theorem pc_not_nac : PolicyCoordination S Λ (pol true true) ∧
    ¬ NaiveActionCoordinationExt prior S T1 T2 false :=
  ⟨pc, not_nac⟩

end CB

/-! ## NAC ∧ ¬PC: three observations -/

namespace Three

/-- The policy points of the world `(state, a₁, a₂, a₃)`. Source: mandate T8(b). Kind: D. Fidelity: n/a -/
def pp₀ (ω : Fin 2 × Bool × Bool × Bool) : Policy threeTables Bool :=
  fun T => if T = X1 then ω.2.1 else if T = X2 then ω.2.2.1 else ω.2.2.2

/-- The number of `b`s (`true`) played. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def nb (ω : Fin 2 × Bool × Bool × Bool) : ℕ :=
  (if ω.2.1 then 1 else 0) + (if ω.2.2.1 then 1 else 0) + (if ω.2.2.2 then 1 else 0)

/-- The symmetric utility: `9` for `aaa` and `bbb`, `10` for one `b`, `0` for two.
Source: mandate T8(b) (the model found here)
Kind: D
Fidelity: n/a -/
def U₀ (ω : Fin 2 × Bool × Bool × Bool) : ℚ :=
  if nb ω = 0 then 9 else if nb ω = 1 then 10 else if nb ω = 2 then 0 else 9

/-- **The prior**: sixteen worlds of mass `1/16` (independent uniform points).
Source: mandate T8(b)
Kind: D
Fidelity: n/a -/
def prior : FiniteBLIPrior witIndex 1 threeTables Bool :=
  handPrior (Fin 2 × Bool × Bool × Bool) (fun _ => 1 / 16) (fun _ => by norm_num)
    (by norm_num [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool])
    (fun ω => if ω.1 = 0 then X1 else X2) three_zeroOne pp₀ U₀

/-- The trivial paper layer. Source: mandate T8(b). Kind: D. Fidelity: n/a -/
def Λ : PaperLayer prior := PaperLayer.trivial prior

/-- The structure (no self-modification). Source: mandate T8(b). Kind: D. Fidelity: n/a -/
def S : PaperStructure threeTables Bool := PaperStructure.plain threeTables Bool

/-- The three-point policy. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def pol (a b c : Bool) : Policy threeTables Bool :=
  fun T => if T = X1 then a else if T = X2 then b else c

/-- The point values. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma pp_X1 (ω : Fin 2 × Bool × Bool × Bool) : prior.pp ω X1 = ω.2.1 := by
  simp [prior, handPrior, pp₀]
/-- The point at `X2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma pp_X2 (ω : Fin 2 × Bool × Bool × Bool) : prior.pp ω X2 = ω.2.2.1 := by
  simp [prior, handPrior, pp₀, mRec_ne_mAsk']
/-- The point at `X3`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma pp_X3 (ω : Fin 2 × Bool × Bool × Bool) : prior.pp ω X3 = ω.2.2.2 := by
  simp [prior, handPrior, pp₀, mZero_ne_mAsk, mZero_ne_mRec]

/-- The event `pp = pol a b c`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pp_eq_pol (ω : Fin 2 × Bool × Bool × Bool) (a b c : Bool) :
    prior.pp ω = pol a b c ↔ ω.2.1 = a ∧ ω.2.2.1 = b ∧ ω.2.2.2 = c := by
  constructor
  · intro h
    exact ⟨by simpa [pol] using congrFun h X1, by simpa [pol, mRec_ne_mAsk'] using congrFun h X2,
      by simpa [pol, mZero_ne_mAsk, mZero_ne_mRec] using congrFun h X3⟩
  · rintro ⟨h₁, h₂, h₃⟩
    funext T
    rcases eq_X1_or_X2_or_X3 T with rfl | rfl | rfl <;>
      simp [pol, mRec_ne_mAsk', mZero_ne_mAsk, mZero_ne_mRec, h₁, h₂, h₃]

/-- **The marginal values**: at every observation `EU o a = 29/4 > 19/4 = EU o b`, both points
of mass `1/2`.
Source: mandate T8(b)
Kind: L
Fidelity: n/a -/
lemma margs (o : ↥threeTables) :
    prior.EU o false = 29 / 4 ∧ prior.EU o true = 19 / 4 ∧
    0 < prior.ppMass o false ∧ 0 < prior.ppMass o true := by
  rcases eq_X1_or_X2_or_X3 o with rfl | rfl | rfl <;>
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · first | unfold FiniteBLIPrior.EU | unfold FiniteBLIPrior.ppMass
    simp only [pp_X1, pp_X2, pp_X3]
    unfold prior
    first | rw [handPrior_condExp] | rw [handPrior_massOf]
    simp only [handPrior, condExp, massOf, integralOf, U₀, nb, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fintype.sum_bool]
    norm_num

/-- **The conditional values**: at every pair `o₁ ≠ o₂` and every conditioning action `a₁`, the
conditional maximizer at `o₁` is `a`: given `a₁ = a`, `19/2 > 5`; given `a₁ = b`, `5 > 9/2`; all
four cells of mass `1/4`.
Source: mandate T8(b)
Kind: L
Fidelity: n/a -/
lemma conds (o₁ o₂ : ↥threeTables) (hne : o₁ ≠ o₂) (a₁ : Bool) :
    cellEU prior o₁ o₂ false a₁ = (if a₁ then 5 else 19 / 2) ∧
    cellEU prior o₁ o₂ true a₁ = (if a₁ then 9 / 2 else 5) ∧
    0 < prior.pairMass o₁ o₂ false a₁ ∧ 0 < prior.pairMass o₁ o₂ true a₁ := by
  rcases eq_X1_or_X2_or_X3 o₁ with rfl | rfl | rfl <;>
  rcases eq_X1_or_X2_or_X3 o₂ with rfl | rfl | rfl <;>
  first
  | exact absurd rfl hne
  | (cases a₁ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · first | unfold cellEU | unfold FiniteBLIPrior.pairMass
      simp only [pp_X1, pp_X2, pp_X3]
      unfold prior
      first | rw [handPrior_condExp] | rw [handPrior_massOf]
      simp only [handPrior, condExp, massOf, integralOf, U₀, nb, Fintype.sum_prod_type,
        Fin.sum_univ_two, Fintype.sum_bool]
      norm_num)

/-- **Extensional Naive Action Coordination holds everywhere**: at every `o₁ ≠ o₂` and every `a₁`,
the conditional and marginal maximizer sets are both `{a}` (unique maximizers).
Source: mandate T8(b)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem nac_all (o₁ o₂ : ↥threeTables) (hne : o₁ ≠ o₂) (a₁ : Bool) :
    NaiveActionCoordinationExt prior S o₁ o₂ a₁ := by
  intro _ a
  obtain ⟨m0, m1, q0, q1⟩ := margs o₁
  obtain ⟨c0, c1, p0, p1⟩ := conds o₁ o₂ hne a₁
  cases a
  · constructor
    · intro _
      refine ⟨q0, fun b _ => ?_⟩
      cases b
      · exact le_refl _
      · rw [m0, m1]; norm_num
    · intro _
      refine ⟨p0, fun b _ => ?_⟩
      cases b
      · exact le_refl _
      · rw [c0, c1]; cases a₁ <;> norm_num
  · constructor
    · rintro ⟨_, h⟩
      have := h false p0
      rw [c0, c1] at this
      cases a₁ <;> norm_num at this
    · rintro ⟨_, h⟩
      have := h false q0
      rw [m0, m1] at this
      norm_num at this

/-- The ex-ante values of `aaa` and `aab`: `9` and `10`. Source: mandate T8(b). Kind: L. Fidelity: n/a -/
lemma procEU_eq : Λ.procEU (pol false false false) = 9 ∧ Λ.procEU (pol false false true) = 10 := by
  refine ⟨?_, ?_⟩ <;>
  · rw [PaperLayer.procEU_eq]
    show condExp prior.μ prior.U (fun ω => prior.pp ω = _) = _
    simp only [pp_eq_pol]
    unfold prior
    rw [handPrior_condExp]
    simp only [handPrior, condExp, massOf, integralOf, U₀, nb, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fintype.sum_bool]
    norm_num

/-- `aab` has positive mass. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma procMass_pos : 0 < Λ.procMass (pol false false true) := by
  rw [PaperLayer.procMass_eq]
  show 0 < massOf prior.μ (fun ω => prior.pp ω = _)
  simp only [pp_eq_pol]
  unfold prior
  rw [handPrior_massOf]
  simp only [handPrior, massOf, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
  norm_num

/-- **Policy Coordination fails** for the fixed point `aaa`: `aab` is better overall (`10 > 9`) but
its point at `o₃` is worse (`19/4 < 29/4`).
Source: mandate T8(b)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem not_pc : ¬ PolicyCoordination S Λ (pol false false false) := by
  intro h
  obtain ⟨v0, v1⟩ := procEU_eq
  obtain ⟨m0, m1, q0, q1⟩ := margs X3
  have h3 : pol false false false X3 = false := by simp [pol, mZero_ne_mAsk, mZero_ne_mRec]
  have h3' : pol false false true X3 = true := by simp [pol, mZero_ne_mAsk, mZero_ne_mRec]
  have := h (pol false false true) (fun _ => Finset.mem_univ _) procMass_pos
    (by rw [v0, v1]; norm_num) X3 (by rw [h3]; exact q0) (by rw [h3']; exact q1)
  rw [h3, h3'] at this
  change prior.EU X3 false ≤ prior.EU X3 true at this
  rw [m0, m1] at this
  norm_num at this

/-- **NAC ⇏ PC** (and neither ties nor correlation are needed): on the three-observation prior
with independent uniform points, the extensional Naive Action Coordination holds at every pair
and every conditioning action with unique maximizers, `aaa` is a UDT 1.0 fixed point, and
Policy Coordination fails.
Source: bli-paper-018; mandate T8(b)
Kind: P
Fidelity: exact (finite model)
Hyps: (a) none -/
theorem nac_not_pc :
    (∀ (o₁ o₂ : ↥threeTables), o₁ ≠ o₂ → ∀ a₁, NaiveActionCoordinationExt prior S o₁ o₂ a₁) ∧
    IsUDT10 S Λ (pol false false false) ∧ ¬ PolicyCoordination S Λ (pol false false false) := by
  refine ⟨nac_all, fun o => ⟨Finset.mem_univ _, fun a _ _ => ?_⟩, not_pc⟩
  obtain ⟨m0, m1, _, _⟩ := margs o
  have ho : pol false false false o = false := by
    rcases eq_X1_or_X2_or_X3 o with rfl | rfl | rfl <;>
      simp [pol, mRec_ne_mAsk', mZero_ne_mAsk, mZero_ne_mRec]
  rw [ho]
  change prior.EU o a ≤ prior.EU o false
  cases a
  · exact le_refl _
  · rw [m0, m1]; norm_num

end Three

end Cleanroom.Udt.UdtPaperTiling
