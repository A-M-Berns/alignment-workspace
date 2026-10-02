import Cleanroom.Udt.UdtPaperTiling.Rules
import Cleanroom.Udt.UdtPaperTiling.Tables

/-!
# `udt-paper-tiling` · ThirdButtonPrior: Coordinated Buttons as a self-trust failure, and the
refutation of naive communicative cloning (T10(d), (e))

* **(d) `CoordButtons`**: a `FiniteBLIPrior` over the rooms `{red = T1, green = T2}` with
  `Act = Bool` (`false = "5"`, `true = "10"`), independent points with `P("10") = q`. For
  `0 < q < 1/3`: "5" is the one-step (UDT 1.0) choice in both rooms (`EU red "10" = 10q <
  5(1 − q) = EU red "5"`), every point is positive, and the value of the policy a pill would
  force (`"10"` in both rooms, ex-ante value `10`) exceeds the fixed point's ex-ante value (`5`):
  UDT 1.0's choice depends on its prior and the pre-copy self prefers the pill (bli-paper-076(a)).
* **(e) `CommClone`**: a paper prior over `{pre = X1, red = X2, green = X3}` with
  `Act = Fin 5` (`0,1,2` the buttons, `3 = pill`, `4 = say10`); the pill is the self-modifying
  action forcing `(10, 10)`, `say10` its twin. Worlds: pill chosen and the rooms forced to
  `(10, 10)` (mass `1/2`); `say10` and both rooms press `20` (mass `1/4`, the best response to the
  other obeying); `say10` and both press `10` (mass `1/4`). `CommunicativeCloning` (bli-paper-075's
  hypothesis for `a₁ = pill`, `cc(pill) = say10`: minimal modification probability and
  `chosenEU pre pill = 𝔼[U | π*(pre) = say10 ∧ followed]`) **holds**, Policy Fairness holds, and the
  naive conclusion — "UDT 1.0 never strictly prefers an action of non-minimal modification
  probability" — **fails**: `chosenEU pre pill = 10 > 5 = chosenEU pre say10` with `modProb pill =
  1 > 0 = modProb say10`.

Package `udt-paper-tiling` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Udt.UdtPaperTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

/-! ## (d) Coordinated Buttons as a self-trust failure -/

namespace CoordButtons

/-- `Rec ≠ Ask`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mRec_ne_mAsk : mRec ≠ mAsk := mAsk_ne_mRec.symm

/-- The product weight `P(red) · P(green)` with `P("10") = q` in each room (halved over the two
states).
Source: bli-paper-076(a)
Kind: D
Fidelity: n/a -/
def w (q : ℚ) (ω : Fin 2 × Bool × Bool) : ℚ :=
  (1 / 2) * ((if ω.2.1 then q else 1 - q) * (if ω.2.2 then q else 1 - q))

/-- The policy points of a world. Source: bli-paper-076(a). Kind: D. Fidelity: n/a -/
def pp₀ (ω : Fin 2 × Bool × Bool) : Policy twoTables Bool :=
  fun T => if T = T1 then ω.2.1 else ω.2.2

/-- The Coordinated Buttons payoff: both "10" ↦ 10, both "5" ↦ 5, else 0.
Source: `main.tex` 129–133; bli-paper-076(a)
Kind: D
Fidelity: exact -/
def U₀ (ω : Fin 2 × Bool × Bool) : ℚ :=
  if ω.2.1 ∧ ω.2.2 then 10 else if ¬ ω.2.1 ∧ ¬ ω.2.2 then 5 else 0

/-- **The Coordinated Buttons prior with independent points `P("10") = q`.**
Source: bli-paper-076(a); `main.tex` 129–133
Kind: D
Fidelity: exact (independent points; the memory-erasure is the two tables) -/
def prior (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : FiniteBLIPrior witIndex 1 twoTables Bool :=
  handPrior (Fin 2 × Bool × Bool) (w q)
    (fun ω => by
      unfold w
      have : 0 ≤ 1 - q := by linarith
      rcases ω with ⟨_, b₁, b₂⟩
      cases b₁ <;> cases b₂ <;> simp <;> positivity)
    (by
      simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, w]
      simp
      ring)
    (fun ω => twoState ω.1) two_zeroOne pp₀ U₀

/-- `EU red "5" = 5(1 − q)` and `EU red "10" = 10q` (for `q < 1`, `0 < q`).
Source: `main.tex` 131–133 ("if it believes that its other instance will probably choose red")
Kind: L
Fidelity: n/a -/
lemma EU_red (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    (prior q h0 h1).EU T1 false = 5 * (1 - q) ∧ (prior q h0 h1).EU T1 true = 10 * q := by
  have hq1' : 1 - q ≠ 0 := by linarith
  have hq0' : q ≠ 0 := ne_of_gt hq0
  constructor <;>
  · unfold FiniteBLIPrior.EU prior
    rw [handPrior_condExp]
    simp only [handPrior, condExp, massOf, integralOf, pp₀, U₀, w, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fintype.sum_bool]
    simp
    try field_simp
    try ring

/-- The same at the green room. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma EU_green (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    (prior q h0 h1).EU T2 false = 5 * (1 - q) ∧ (prior q h0 h1).EU T2 true = 10 * q := by
  have hq1' : 1 - q ≠ 0 := by linarith
  have hq0' : q ≠ 0 := ne_of_gt hq0
  constructor <;>
  · unfold FiniteBLIPrior.EU prior
    rw [handPrior_condExp]
    simp only [handPrior, condExp, massOf, integralOf, pp₀, U₀, w, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fintype.sum_bool]
    simp [mRec_ne_mAsk]
    try field_simp
    try ring

/-- The ex-ante values of the two constant policies: both "10" ↦ `10`, both "5" ↦ `5`.
Source: bli-paper-076(a) (the pill's value and the fixed point's)
Kind: L
Fidelity: n/a -/
lemma exAnte (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    (prior q h0 h1).exAnteValue (fun _ => true) = 10 ∧
    (prior q h0 h1).exAnteValue (fun _ => false) = 5 := by
  have hq1' : 1 - q ≠ 0 := by linarith
  have hq0' : q ≠ 0 := ne_of_gt hq0
  have key : ∀ (ω : Fin 2 × Bool × Bool) (c : Bool), pp₀ ω = (fun _ => c) ↔ ω.2.1 = c ∧ ω.2.2 = c := by
    intro ω c
    constructor
    · intro h
      exact ⟨by simpa [pp₀] using congrFun h T1, by simpa [pp₀, mRec_ne_mAsk] using congrFun h T2⟩
    · rintro ⟨h₁, h₂⟩
      funext T
      rcases eq_T1_or_T2 T with rfl | rfl <;> simp [pp₀, mRec_ne_mAsk, h₁, h₂]
  constructor <;>
  · unfold FiniteBLIPrior.exAnteValue prior
    rw [handPrior_condExp]
    simp only [handPrior, condExp, massOf, integralOf, key, U₀, w, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fintype.sum_bool]
    simp
    try field_simp
    try ring

/-- Every point is positive (`NDPOL`). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma ndpol (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) : (prior q h0 h1).NDPOL := by
  intro T a
  have hq1' : 0 < 1 - q := by linarith
  unfold FiniteBLIPrior.ppMass prior
  rw [handPrior_massOf]
  rcases eq_T1_or_T2 T with rfl | rfl <;> cases a <;>
  · simp only [handPrior, massOf, pp₀, w, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
    simp [mRec_ne_mAsk]
    nlinarith

/-- **Coordinated Buttons as a self-trust failure** (bli-paper-076(a)): for `0 < q < 1/3`, "5" is
the one-step choice in both rooms (strictly: `10q < 5(1 − q)`), every point is positive, and the
policy the pill would force (both "10") has ex-ante value `10 > 5`, the value of the fixed point
`(5, 5)`. UDT 1.0's choice depends on its prior; the pre-copy self prefers the pill.
Source: [[udt-tiling-working-notes-2025-06-30]] l5, LaTeX draft lines 787–829 (bli-paper-076(a));
`main.tex` 129–133
Kind: N+
Fidelity: exact
Hyps: (a) `0 < q < 1/3` -/
theorem selfTrust_failure (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (hq0 : 0 < q) (hq : q < 1 / 3) :
    (prior q h0 h1).IsOneStepChoice T1 false ∧ (prior q h0 h1).IsOneStepChoice T2 false ∧
    (prior q h0 h1).EU T1 true < (prior q h0 h1).EU T1 false ∧ (prior q h0 h1).NDPOL ∧
    (prior q h0 h1).exAnteValue (fun _ => true) = 10 ∧
    (prior q h0 h1).exAnteValue (fun _ => false) = 5 := by
  have hq1 : q < 1 := by linarith
  obtain ⟨r5, r10⟩ := EU_red q h0 h1 hq0 hq1
  obtain ⟨g5, g10⟩ := EU_green q h0 h1 hq0 hq1
  obtain ⟨e10, e5⟩ := exAnte q h0 h1 hq0 hq1
  refine ⟨fun b => ?_, fun b => ?_, ?_, ndpol q h0 h1 hq0 hq1, e10, e5⟩
  · cases b
    · exact le_refl _
    · rw [r5, r10]; linarith
  · cases b
    · exact le_refl _
    · rw [g5, g10]; linarith
  · rw [r5, r10]; linarith

end CoordButtons

/-! ## (e) The refutation of naive communicative cloning -/

namespace CommClone

/-- The three-point policy `pre ↦ a`, `red ↦ b`, `green ↦ c`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def polE (a b c : Fin 5) : Policy threeTables (Fin 5) :=
  fun T => if T = X1 then a else if T = X2 then b else c

/-- `polE a b c pre = a`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma polE_X1 (a b c : Fin 5) : polE a b c X1 = a := by simp [polE]
/-- `polE a b c red = b`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma polE_X2 (a b c : Fin 5) : polE a b c X2 = b := by simp [polE, mRec_ne_mAsk']
/-- `polE a b c green = c`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma polE_X3 (a b c : Fin 5) : polE a b c X3 = c := by simp [polE, mZero_ne_mAsk, mZero_ne_mRec]

/-- `polE` is injective. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma polE_inj {a b c a' b' c' : Fin 5} : polE a b c = polE a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · intro h
    exact ⟨by simpa using congrFun h X1, by simpa using congrFun h X2, by simpa using congrFun h X3⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- The paper's `eff` for this problem: the pill forces `(10, 10)` and becomes `say10`.
Source: bli-paper-075/076(c)
Kind: D
Fidelity: n/a -/
def effE (π : Policy threeTables (Fin 5)) : Policy threeTables (Fin 5) :=
  if π X1 = 3 then polE 4 1 1 else π

/-- The chosen policy by world index: `0 ↦ (pill, 20, 20)`, `1 ↦ (say10, 20, 20)`,
`2 ↦ (say10, 10, 10)`.
Source: mandate T10(e)
Kind: D
Fidelity: n/a -/
def chosen₀ : Fin 3 → Policy threeTables (Fin 5)
  | 0 => polE 3 2 2
  | 1 => polE 4 2 2
  | 2 => polE 4 1 1

/-- The masses by index (halved over the two states): `1/2, 1/4, 1/4`.
Source: mandate T10(e)
Kind: D
Fidelity: n/a -/
def w : Fin 3 → ℚ
  | 0 => 1 / 4
  | 1 => 1 / 8
  | 2 => 1 / 8

/-- The utility: the Third Button payoff of the effective room points — `10` when both press
"10", `0` when both press "20".
Source: mandate T10(e)
Kind: D
Fidelity: n/a -/
def u : Fin 3 → ℚ
  | 0 => 10
  | 1 => 0
  | 2 => 10

/-- **The communicative-cloning prior.** Source: mandate T10(e). Kind: D. Fidelity: n/a -/
def prior : FiniteBLIPrior witIndex 1 threeTables (Fin 5) :=
  handPrior (Fin 2 × Fin 3) (fun ω => w ω.2) (fun ω => by
      rcases ω with ⟨_, i⟩; match i with | 0 | 1 | 2 => norm_num [w])
    (by simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]; norm_num [w])
    (fun ω => if ω.1 = 0 then X1 else X2) three_zeroOne (fun ω => effE (chosen₀ ω.2)) (fun ω => u ω.2)

/-- The paper layer. Source: mandate T10(e). Kind: D. Fidelity: n/a -/
def Λ : PaperLayer prior where
  chosen := fun ω => chosen₀ ω.2
  eff := effE
  pp_eff := fun _ => rfl

/-- **The modification probability of an action at `o`**: `P(π* ≠ π# | π*(o) = a)` (junk `0` at a
null point).
Source: [[udt-tiling-working-notes-2025-06-30]] l13 ("the modification probability `m_μ(o, a)`")
(bli-paper-074/075)
Kind: D
Fidelity: variant: the message set is not modelled; "modified" is `π* ≠ π#` -/
def modProb {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {Act : Type} [Fintype Act]
    [DecidableEq Act] {P : FiniteBLIPrior 𝒮 m 𝒟 Act} (Λ : PaperLayer P) (o : ↥𝒟) (a : Act) : ℚ :=
  massOf P.μ (fun ω => Λ.chosen ω o = a ∧ Λ.chosen ω ≠ P.pp ω) / Λ.pointMass o a

/-- **Communicative Cloning for `a₁` with clone `cc`** (bli-paper-075's hypothesis): the clone's
point is positive, `cc` has minimal modification probability among the positive available
actions at `o`, and the value of `a₁` equals the value of `cc` conditioned on the recommendation
being followed. The positivity guard on `cc` (repair round 2, fidelity N-3) closes a junk hole:
`modProb` is `0` at a null point, so a null clone would be "of minimal modification probability"
vacuously. "Followed" stands in for the notes' `[π† ≡ μ†]_{−o}` — a modelling substitution,
**(c)**: the message set and the listeners' policies `μ†` are not modelled, and the event is
supplied by the user of the predicate (on the refutation model it is the natural one, both rooms
pressing "10").
Source: bli-paper-075 (`m(o, cc(a₁)) = min_{a₂} m(o, a₂)` and
`E(u | π*(o) = a₁) = E(u | π*(o) = cc(a₁) ∧ [π† ≡ μ†]_{−o})`)
Kind: D
Fidelity: variant: the clone's point guarded positive; "followed" is a parameter event (c); the
message set is not modelled -/
def CommunicativeCloning {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {Act : Type}
    [Fintype Act] [DecidableEq Act] {P : FiniteBLIPrior 𝒮 m 𝒟 Act} (Λ : PaperLayer P)
    (S : PaperStructure 𝒟 Act) (o : ↥𝒟) (a₁ cc : Act) (followed : P.Ω → Prop)
    [DecidablePred followed] : Prop :=
  0 < Λ.pointMass o cc ∧
  (∀ a ∈ S.Aof o, 0 < Λ.pointMass o a → modProb Λ o cc ≤ modProb Λ o a) ∧
  Λ.chosenEU o a₁ = condExp P.μ P.U (fun ω => Λ.chosen ω o = cc ∧ followed ω)

/-- The structure: `𝒜_pre = {pill, say10}`, `𝒜_room = {"5", "10", "20"}`, `𝒜^m = {pill}`,
`p̂ill = say10`, `mod pill = {(red, "10"), (green, "10")}`.
Source: mandate T10(e)
Kind: D
Fidelity: n/a -/
def S : PaperStructure threeTables (Fin 5) where
  Aof := fun T => if T = X1 then {3, 4} else {0, 1, 2}
  selfMod := {3}
  twin := fun a => if a = 3 then 4 else a
  twin_nonMod := by decide
  twin_typed := by
    intro a T ha
    by_cases hT : T = X1
    · simp only [hT, if_true] at ha ⊢
      fin_cases a <;> simp_all
    · simp only [hT, if_false] at ha ⊢
      fin_cases a <;> simp_all
  twin_id := by intro a ha; fin_cases a <;> simp_all
  mod := fun a T => if a = 3 ∧ T ≠ X1 then some 1 else none
  mod_nonMod_none := by intro a ha T; fin_cases a <;> simp_all

/-- The chosen coordinate. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma Λ_chosen (ω : Fin 2 × Fin 3) : Λ.chosen ω = chosen₀ ω.2 := rfl

/-- "Followed": both rooms press "10". Source: mandate T10(e). Kind: D. Fidelity: n/a -/
def followed (ω : prior.Ω) : Prop := prior.pp ω X2 = 1 ∧ prior.pp ω X3 = 1

instance : DecidablePred followed := fun ω => by unfold followed; infer_instance

/-- `(3 : Fin 5) ≠ 4` and friends. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma h34 : (3 : Fin 5) ≠ 4 := by decide
/-- `(1 : Fin 5) ≠ 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma h12 : (1 : Fin 5) ≠ 2 := by decide
/-- `(0 : Fin 3) ≠ 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma f01 : (0 : Fin 3) ≠ 1 := by decide
/-- `(0 : Fin 3) ≠ 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma f02 : (0 : Fin 3) ≠ 2 := by decide
/-- `(1 : Fin 3) ≠ 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma f12 : (1 : Fin 3) ≠ 2 := by decide

/-- The effective policies by index. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma effE_chosen : effE (chosen₀ 0) = polE 4 1 1 ∧ effE (chosen₀ 1) = polE 4 2 2 ∧
    effE (chosen₀ 2) = polE 4 1 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [effE, chosen₀, h34.symm]

/-- The numbers: point masses at `pre`, the chosen-point values, the modification probabilities,
and the cloning identity's right side.
Source: mandate T10(e)
Kind: L
Fidelity: n/a -/
lemma numbers :
    Λ.pointMass X1 3 = 1 / 2 ∧ Λ.pointMass X1 4 = 1 / 2 ∧
    Λ.chosenEU X1 3 = 10 ∧ Λ.chosenEU X1 4 = 5 ∧
    modProb Λ X1 3 = 1 ∧ modProb Λ X1 4 = 0 ∧
    condExp prior.μ prior.U (fun ω => Λ.chosen ω X1 = 4 ∧ followed ω) = 10 := by
  obtain ⟨e0, e1, e2⟩ := effE_chosen
  have hpp : ∀ ω : Fin 2 × Fin 3, prior.pp ω = effE (chosen₀ ω.2) := fun _ => rfl
  have hm3 : Λ.pointMass X1 3 = 1 / 2 := by
    unfold PaperLayer.pointMass prior
    rw [handPrior_massOf]
    simp only [handPrior, massOf, Λ_chosen, chosen₀, polE_X1, w, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [h34, h34.symm]
  have hm4 : Λ.pointMass X1 4 = 1 / 2 := by
    unfold PaperLayer.pointMass prior
    rw [handPrior_massOf]
    simp only [handPrior, massOf, Λ_chosen, chosen₀, polE_X1, w, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [h34, h34.symm]
  refine ⟨hm3, hm4, ?_, ?_, ?_, ?_, ?_⟩
  · unfold PaperLayer.chosenEU prior
    rw [handPrior_condExp]
    simp only [handPrior, condExp, massOf, integralOf, Λ_chosen, chosen₀, polE_X1, w, u,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [h34, h34.symm]
  · unfold PaperLayer.chosenEU prior
    rw [handPrior_condExp]
    simp only [handPrior, condExp, massOf, integralOf, Λ_chosen, chosen₀, polE_X1, w, u,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [h34, h34.symm]
  · unfold modProb
    rw [hm3]
    unfold prior
    rw [handPrior_massOf]
    simp only [handPrior, massOf, Λ_chosen, chosen₀, polE_X1, w, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three, effE, polE_inj]
    norm_num [polE_inj, h34, h34.symm, h12, h12.symm]
  · unfold modProb
    rw [hm4]
    unfold prior
    rw [handPrior_massOf]
    simp only [handPrior, massOf, Λ_chosen, chosen₀, polE_X1, w, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three, effE, polE_inj]
    norm_num [polE_inj, h34, h34.symm, h12, h12.symm]
  · unfold followed
    simp only [hpp]
    unfold prior
    rw [handPrior_condExp]
    simp only [handPrior, condExp, massOf, integralOf, Λ_chosen, chosen₀, polE_X1, polE_X2,
      polE_X3, w, u, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, effE]
    norm_num [polE_inj, h34, h34.symm, h12, h12.symm]

/-- The positive chosen policies. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pos_cases {π : Policy threeTables (Fin 5)} (h : 0 < Λ.procMass π) :
    π = polE 3 2 2 ∨ π = polE 4 2 2 ∨ π = polE 4 1 1 := by
  rw [PaperLayer.procMass_eq] at h
  obtain ⟨ω, hω, _⟩ := (massOf_pos_iff prior.μ prior.μ_nonneg _).mp h
  rw [Λ_chosen] at hω
  rw [← hω]
  rcases ω with ⟨_, i⟩
  match i with
  | 0 => simp [chosen₀]
  | 1 => simp [chosen₀]
  | 2 => simp [chosen₀]

/-- The values of the three chosen policies. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma procEU_eq : Λ.procEU (polE 3 2 2) = 10 ∧ Λ.procEU (polE 4 2 2) = 0 ∧
    Λ.procEU (polE 4 1 1) = 10 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [PaperLayer.procEU_eq]
    unfold prior
    rw [handPrior_condExp]
    simp only [handPrior, condExp, massOf, integralOf, Λ_chosen, chosen₀, polE_inj, w, u,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [polE_inj, h34, h34.symm, h12, h12.symm]

/-- **Policy Fairness holds on the cloning prior**: `(pill, 20, 20)` and `(say10, 10, 10)` share the
effective policy `(say10, 10, 10)` and the value `10`.
Source: mandate T10(e)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem policyFair : prior.PolicyFair Λ.toProcLayer := by
  intro p q hpq hp hq
  have hpq' : effE p = effE q := hpq
  show Λ.procEU p = Λ.procEU q
  obtain ⟨v0, v1, v2⟩ := procEU_eq
  rcases pos_cases hp with rfl | rfl | rfl <;> rcases pos_cases hq with rfl | rfl | rfl <;>
    simp [effE, polE_inj, h34.symm] at hpq' <;> simp [v0, v1, v2]

/-- **Naive communicative cloning is refuted** (bli-paper-075's intended theorem, 076(c)):
Communicative Cloning holds for `a₁ = pill` with clone `say10` (`say10` has modification
probability `0`, the minimum; `chosenEU pre pill = 10 = 𝔼[U | π*(pre) = say10 ∧ followed]`),
Policy Fairness holds, yet UDT 1.0 at `pre` strictly prefers the pill — an action of non-minimal
modification probability (`1 > 0`) — to `say10`: `10 > 5`. Self-modification is a stronger
coordination tool than self-signalling when the listeners best-respond to the message.
Source: [[udt-tiling-working-notes-2025-06-30]] l10 §Counterexample, l13 "Proof" (bli-paper-075,
076(c))
Kind: P
Fidelity: exact (refutation by a finite model; the message set is not modelled —
`CommunicativeCloning`'s "followed" is the event that both rooms press "10")
Hyps: (a) none -/
theorem naive_cloning_refuted :
    CommunicativeCloning Λ S X1 3 4 followed ∧ prior.PolicyFair Λ.toProcLayer ∧
    modProb Λ X1 4 < modProb Λ X1 3 ∧ Λ.chosenEU X1 4 < Λ.chosenEU X1 3 ∧
    3 ∈ S.Aof X1 ∧ 4 ∈ S.Aof X1 ∧ 0 < Λ.pointMass X1 3 ∧ 0 < Λ.pointMass X1 4 := by
  obtain ⟨m3, m4, v3, v4, p3, p4, cc⟩ := numbers
  refine ⟨⟨by rw [m4]; norm_num, fun a ha hpos => ?_, by rw [v3, cc]⟩, policyFair,
    by rw [p3, p4]; norm_num,
    by rw [v3, v4]; norm_num, by simp [S], by simp [S], by rw [m3]; norm_num, by rw [m4]; norm_num⟩
  rw [p4]
  unfold modProb
  exact div_nonneg (massOf_nonneg _ prior.μ_nonneg _) (massOf_nonneg _ prior.μ_nonneg _)

end CommClone

end Cleanroom.Udt.UdtPaperTiling
