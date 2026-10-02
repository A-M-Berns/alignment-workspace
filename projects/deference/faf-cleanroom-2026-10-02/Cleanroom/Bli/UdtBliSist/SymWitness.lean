import Cleanroom.Bli.UdtBliSist.FourTables
import Cleanroom.Bli.UdtBliSist.Freedom

/-!
# `udt-bli-sist` · SymWitness: the two-ask-table family — the N+ of the symmetric model (T2 a)

Repair round 1, A1: `sist_symmetric` / `sist_sign_symmetric` shipped without an inhabitant of
their package. **The family** `symPrior w ρ c V r₀` over `fourTables` (`Ask₁ = (1,0)`,
`Ask₂ = (1,1)`, `Rec = (0,1)`, `Other = (0,0)`): base `Fin 4 × Bool` (the state index and
**Omega's pick bit** `J`: `false ↦ Ask₁`, `true ↦ Ask₂`, uniform and independent of the state),
masses `w s / 2`; policy law the pushforward of `(a₁, a₂, r, o) ↦ pairρ ρ a₁ a₂ · 1/4` — the two
Ask points agree with probability `(1+ρ)/2`, the Rec and Other points independent uniform; the
SIST utility (`−c` at an Ask table for `give`, `V` at Rec for `give` at Omega's pick, `r₀` at
Other), observed table `Q = Ask₁`.

* `symmetric_tie`: with equal Ask masses `w 0 = w 1`, the symmetric model's defining tie
  `pickMass T · μ(Ask) = μ(state = T) · μ(Rec)` holds at both Ask tables — the hypothesis of
  `sist_symmetric` is **inhabited**, not assumed;
* `pointCorr_both`: the bracket `δ_{Ask₁}(Ask₂) = ρ` (and `δ_{Ask₁}(Ask₁) = 1`), so the class
  profile is `ρ̄ = (1 + ρ)/2` (`classProfile_eq`) — **strictly between `0` and `1`** for
  `−1 < ρ < 1`;
* `verdict`: `EU Ask₁ give − EU Ask₁ refuse = (V·μ(Rec) − c·μ(Ask)) · (1+ρ)/2 + μ(Other)·Δr₀`,
  by `sist_symmetric`; `sign`: the sign is `ρ`-free for `ρ > −1` (`sist_sign_symmetric`);
* `instance_half`: at `ρ = 1/2`, masses `(49/200, 49/200, 49/100, 2/100)`, `(100, 10)`:
  `ρ̄ = 3/4`, the difference is `1323/40 + (2/100)·Δr₀`, one-step pays strictly for `|r₀| ≤ 10`;
* `not_hPoint`, `not_hUnif`: the family is outside both degenerate regimes (`H_point` fails
  because `Ask₂` has mass; `H_unif` fails for `ρ < 1`).

Sources: bli-soto-b-2-006 ("a clean N+ witness with `N = 2`"); journal l. 291; mandate T2(a);
audit round 1 A1 (the fidelity and adversarial audits both asked for this family).
-/

namespace Cleanroom.Bli.UdtBliSist

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliCore.Mugging Finset
open Freedom (pairρ)

namespace Sym2

/-! ## The branch predicates on `fourTables` -/

/-- **The Ask predicate**: the table prices the coin at `1` (`Ask₁` and `Ask₂`).
Source: mandate §3.2 (`Ask T := T.1 coin = 1`)
Kind: D
Fidelity: exact -/
def askP (T : ↥fourTables) : Prop := T.1 pS = 1

/-- **The Rec predicate**: the coin at `0` and `q` at `1` (the `Rec` table).
Source: mandate §3.2
Kind: D
Fidelity: exact -/
def recP (T : ↥fourTables) : Prop := T.1 pS = 0 ∧ T.1 qS = 1

/-- `askP` is decidable.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance askP.decidable : DecidablePred askP := fun T => inferInstanceAs (Decidable (T.1 pS = 1))

/-- `recP` is decidable.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance recP.decidable : DecidablePred recP :=
  fun T => inferInstanceAs (Decidable (T.1 pS = 0 ∧ T.1 qS = 1))

/-- `Ask₁` is ask-like.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma askP_fAsk : askP fAsk := by simp [askP, mAsk]

/-- `Ask₂` is ask-like.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma askP_fBoth : askP fBoth := by simp [askP, mBoth]

/-- `Rec` is not ask-like.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma not_askP_fRec : ¬ askP fRec := by simp [askP, mRec]

/-- `Other` is not ask-like.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma not_askP_fOther : ¬ askP fOther := by simp [askP, mOther]

/-- `Rec` is rec-like.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma recP_fRec : recP fRec := by simp [recP, mRec, pW_ne_qW.symm]

/-- `Other` is not rec-like.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma not_recP_fOther : ¬ recP fOther := by simp [recP, mOther]

/-! ## The correlated law on the four points -/

/-- The parameter type: the values at `Ask₁`, `Ask₂`, `Rec`, `Other`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev K : Type := Bool × Bool × Bool × Bool

/-- The policy with the given values at the four tables.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def smk (k : K) : Policy fourTables Bool :=
  fun T => if T = fAsk then k.1 else if T = fBoth then k.2.1 else if T = fRec then k.2.2.1
    else k.2.2.2

/-- `smk k Ask₁ = k.1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma smk_fAsk (k : K) : smk k fAsk = k.1 := by simp [smk]

/-- `smk k Ask₂ = k.2.1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma smk_fBoth (k : K) : smk k fBoth = k.2.1 := by simp [smk, fAsk_ne_fBoth.symm]

/-- `smk k Rec = k.2.2.1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma smk_fRec (k : K) : smk k fRec = k.2.2.1 := by
  simp [smk, fAsk_ne_fRec.symm, fBoth_ne_fRec.symm]

/-- `smk k Other = k.2.2.2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma smk_fOther (k : K) : smk k fOther = k.2.2.2 := by
  simp [smk, fAsk_ne_fOther.symm, fBoth_ne_fOther.symm, fRec_ne_fOther.symm]

/-- The weights: the pair law `pairρ ρ` on `(Ask₁, Ask₂)` times uniform on `(Rec, Other)`.
Source: bli-soto-b-2-006 (the `N = 2` witness: two correlated ask points); mandate T4's `pairρ`
Kind: D
Fidelity: exact -/
def sg (ρ : ℚ) (k : K) : ℚ := pairρ ρ k.1 k.2.1 * (1 / 4)

/-- `sg ≥ 0` for `|ρ| ≤ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sg_nonneg {ρ : ℚ} (hρ : |ρ| ≤ 1) (k : K) : 0 ≤ sg ρ k := by
  have h := abs_le.mp hρ
  unfold sg pairρ
  split_ifs <;> linarith

/-- `∑ sg = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_sg (ρ : ℚ) : ∑ k : K, sg ρ k = 1 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, sg, pairρ]
  simp
  ring

/-! ## The family -/

/-- **Omega's pick**: the pick bit selects `Ask₂` (`true`) or `Ask₁` (`false`).
Source: bli-soto-b-2-006 (`J` distributed over the ask tables); mandate §3.5
Kind: D
Fidelity: exact -/
def symJ (ω : Fin 4 × Bool) : ↥fourTables := if ω.2 then fBoth else fAsk

/-- The reference table: an Ask state reads its own table, a Rec state Omega's pick, the residual
state the observed table `Ask₁`.
Source: mandate §3.5
Kind: D
Fidelity: exact -/
def symRef (ω : Fin 4 × Bool) : ↥fourTables :=
  if askP (fourState ω.1) then fourState ω.1 else if recP (fourState ω.1) then symJ ω else fAsk

/-- The payoff: `−c` for `give` at an Ask table, `V` for `give` at Rec, `r₀ b` at Other.
Source: bli-soto-a-077 (the four cases); mandate T2
Kind: D
Fidelity: exact -/
def symPay (c V : ℚ) (r₀ : Bool → ℚ) (ω : Fin 4 × Bool) (b : Bool) : ℚ :=
  if askP (fourState ω.1) then -c * ind b
  else if recP (fourState ω.1) then V * ind b else r₀ b

variable (w : Fin 4 → ℚ) (hw : ∀ s, 0 ≤ w s) (hw1 : ∑ s, w s = 1) (ρ : ℚ) (hρ : |ρ| ≤ 1)
  (c V : ℚ) (r₀ : Bool → ℚ)

/-- **The two-ask-table SIST data**: base `Fin 4 × Bool` with masses `w s / 2` (the pick bit
uniform), the four tables, `0/1` faith, the `pairρ`-correlated law on the two Ask points, the
SIST payoff read at `symRef`.
Source: bli-soto-b-2-006; mandate T2 (`sistData N w J ν` at `N = 2`)
Kind: D
Fidelity: exact (finite; `w` the masses, `ρ` the correlation of the two Ask points) -/
def symData : IndepData witIndex 1 fourTables Bool where
  Ω₀ := Fin 4 × Bool
  μ₀ := fun ω => w ω.1 / 2
  μ₀_nonneg := fun ω => by have := hw ω.1; positivity
  μ₀_sum_one := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    rw [← hw1]
    apply Finset.sum_congr rfl
    intro s _
    ring
  state₀ := fun ω => fourState ω.1
  small₀ := fun ω φ => decide ((fourState ω.1).1 φ = 1)
  faith₀ := faith_of_zeroOne _ _ four_zeroOne
  ν := pushLaw smk (sg ρ)
  ν_nonneg := pushLaw_nonneg _ _ (sg_nonneg hρ)
  ν_sum_one := by rw [sum_pushLaw, sum_sg]
  U₀ := fun ω π => symPay c V r₀ ω (π (symRef ω))

/-- **The two-ask-table SIST prior** (the N+ of the symmetric model).
Source: bli-soto-b-2-006; mandate T2(a)
Kind: D
Fidelity: exact -/
def symPrior : FiniteBLIPrior witIndex 1 fourTables Bool := (symData w hw hw1 ρ hρ c V r₀).toPrior

/-- The state coordinate of the data.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma state₀_eq (ω : Fin 4 × Bool) :
    (symData w hw hw1 ρ hρ c V r₀).state₀ ω = fourState ω.1 := rfl

/-- The base law of the data.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma μ₀_eq (ω : Fin 4 × Bool) : (symData w hw hw1 ρ hρ c V r₀).μ₀ ω = w ω.1 / 2 := rfl

/-- Sums over the base are sums over `Fin 4 × Bool`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_base (f : Fin 4 × Bool → ℚ) :
    (∑ ω : (symData w hw hw1 ρ hρ c V r₀).Ω₀, f ω) = ∑ ω : Fin 4 × Bool, f ω := rfl

/-- **The family has the SIST shape** with `Ask = askP`, `Rec = recP`, Omega's pick `symJ`,
observed table `Ask₁`, constant stakes, residual `r₀`.
Source: mandate T2
Kind: L
Fidelity: exact -/
lemma shaped : SistShaped (symData w hw hw1 ρ hρ c V r₀) askP recP symJ fAsk
    (fun _ => c) (fun _ => V) (fun _ b => r₀ b) :=
  fun _ _ => rfl

/-- Every point of the family has `ν`-mass `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_point (T : ↥fourTables) (a : Bool) :
    massOf (symData w hw hw1 ρ hρ c V r₀).ν (fun π => π T = a) = 1 / 2 := by
  change massOf (pushLaw smk (sg ρ)) (fun π => π T = a) = 1 / 2
  rw [massOf_pushLaw]
  rcases eq_four T with rfl | rfl | rfl | rfl <;>
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, smk_fAsk, smk_fBoth, smk_fRec, smk_fOther,
      sg, pairρ] <;>
    cases a <;> (simp; try ring)

/-- Every policy point of the prior has mass `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ppMass_eq (T : ↥fourTables) (a : Bool) :
    (symData w hw hw1 ρ hρ c V r₀).toPrior.ppMass T a = 1 / 2 := by
  rw [IndepData.ppMass_toPrior, massOf_point]

/-- **The pair law of the two Ask points** is `pairρ ρ`: `μ(pp·Ask₂ = b ∧ pp·Ask₁ = a) = pairρ ρ a b`.
Source: bli-soto-b-2-006; mandate T4 (`ν(gg) = ν(rr) = (1+ρ)/4`, …)
Kind: L
Fidelity: exact -/
lemma pairMass_both_ask (b a : Bool) :
    (symData w hw hw1 ρ hρ c V r₀).toPrior.pairMass fBoth fAsk b a = pairρ ρ a b := by
  rw [IndepData.pairMass_toPrior]
  change massOf (pushLaw smk (sg ρ)) (fun π => π fBoth = b ∧ π fAsk = a) = _
  rw [massOf_pushLaw]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, smk_fAsk, smk_fBoth, sg]
  cases a <;> cases b <;> simp [pairρ] <;> ring

/-- **The bracket at the second Ask table is `ρ`**: `δ_{Ask₁}(Ask₂) = ρ`.
Source: bli-soto-b-2-006 (the bracket `P(A_j = give | A_i = give) − P(A_j = give | A_i = refuse)`)
Kind: P
Fidelity: exact -/
theorem pointCorr_both :
    pointCorr (symData w hw hw1 ρ hρ c V r₀).toPrior fAsk fBoth true false = ρ := by
  unfold pointCorr condPoint
  rw [pairMass_both_ask, pairMass_both_ask, ppMass_eq, ppMass_eq]
  simp [pairρ]
  ring

/-- `δ_{Ask₁}(Ask₁) = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pointCorr_ask :
    pointCorr (symData w hw hw1 ρ hρ c V r₀).toPrior fAsk fAsk true false = 1 :=
  pointCorr_self _ fAsk true false (by decide)
    (by rw [ppMass_eq]; norm_num) (by rw [ppMass_eq]; norm_num)

/-- The base mass of each state index is `w s`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_state (s : Fin 4) :
    massOf (symData w hw hw1 ρ hρ c V r₀).μ₀
      (fun ω => (symData w hw hw1 ρ hρ c V r₀).state₀ ω = fourState s) = w s := by
  unfold massOf
  rw [sum_base, Fintype.sum_prod_type]
  simp only [state₀_eq, μ₀_eq, Fintype.sum_bool, fourState_eq_iff]
  fin_cases s <;> simp [Fin.sum_univ_four]

/-- The state mass of each table is its base weight.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateMass_eq (s : Fin 4) :
    (symData w hw hw1 ρ hρ c V r₀).toPrior.stateMass (fourState s) = w s := by
  rw [IndepData.stateMass_toPrior, massOf_state]

/-- `μ(Ask) = w 0 + w 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma askMass_eq : askMass (symData w hw hw1 ρ hρ c V r₀) askP = w 0 + w 1 := by
  unfold askMass
  rw [sum_base, Fintype.sum_prod_type]
  simp only [state₀_eq, μ₀_eq, Fintype.sum_bool, Fin.sum_univ_four, fourState_zero, fourState_one,
    fourState_two, fourState_three, askP_fAsk, askP_fBoth, not_askP_fRec, not_askP_fOther, if_true,
    if_false]
  ring

/-- `μ(Rec) = w 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma recMass_eq : recMass (symData w hw hw1 ρ hρ c V r₀) askP recP = w 2 := by
  unfold recMass
  rw [sum_base, Fintype.sum_prod_type]
  simp only [state₀_eq, μ₀_eq, Fintype.sum_bool, Fin.sum_univ_four, fourState_zero, fourState_one,
    fourState_two, fourState_three, askP_fAsk, askP_fBoth, not_askP_fRec, not_askP_fOther,
    recP_fRec, not_recP_fOther, if_true, if_false]
  ring

/-- The residual term is `w 3 · (r₀ give − r₀ refuse)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma resTerm_eq :
    resTerm (symData w hw hw1 ρ hρ c V r₀) askP recP (fun _ b => r₀ b) =
      w 3 * (r₀ true - r₀ false) := by
  unfold resTerm
  rw [sum_base, Fintype.sum_prod_type]
  simp only [state₀_eq, μ₀_eq, Fintype.sum_bool, Fin.sum_univ_four, fourState_zero, fourState_one,
    fourState_two, fourState_three, askP_fAsk, askP_fBoth, not_askP_fRec, not_askP_fOther,
    recP_fRec, not_recP_fOther, if_true, if_false]
  ring

/-- Omega's pick lands on `Ask₁` with mass `w 2 / 2` in the Rec branch.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pickMass_fAsk : pickMass (symData w hw hw1 ρ hρ c V r₀) askP recP symJ fAsk = w 2 / 2 := by
  unfold pickMass
  rw [sum_base, Fintype.sum_prod_type]
  simp only [state₀_eq, μ₀_eq, Fintype.sum_bool, Fin.sum_univ_four, fourState_zero, fourState_one,
    fourState_two, fourState_three, askP_fAsk, askP_fBoth, not_askP_fRec, not_askP_fOther,
    recP_fRec, not_recP_fOther, symJ, if_true, if_false, true_and, false_and,
    Bool.false_eq_true, fAsk_ne_fBoth.symm]
  simp

/-- Omega's pick lands on `Ask₂` with mass `w 2 / 2` in the Rec branch.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pickMass_fBoth : pickMass (symData w hw hw1 ρ hρ c V r₀) askP recP symJ fBoth = w 2 / 2 := by
  unfold pickMass
  rw [sum_base, Fintype.sum_prod_type]
  simp only [state₀_eq, μ₀_eq, Fintype.sum_bool, Fin.sum_univ_four, fourState_zero, fourState_one,
    fourState_two, fourState_three, askP_fAsk, askP_fBoth, not_askP_fRec, not_askP_fOther,
    recP_fRec, not_recP_fOther, symJ, if_true, if_false, true_and, false_and,
    Bool.false_eq_true, fAsk_ne_fBoth]
  simp

/-- Omega's pick lands in the Ask class.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma hJ : ∀ ω₀, recP ((symData w hw hw1 ρ hρ c V r₀).state₀ ω₀) → askP (symJ ω₀) := by
  intro ω _
  unfold symJ
  split_ifs <;> simp

/-! ## The symmetric model is inhabited -/

/-- **The symmetry tie holds** with equal Ask masses: at both Ask tables,
`pickMass T · μ(Ask) = μ(state = T) · μ(Rec)` (`(w 2 / 2)·(w 0 + w 1) = w 0 · w 2`).
Source: bli-soto-b-2-006 ("the Ask-branch weighting of the `j`-tables is the same law as `J`");
mandate T2(a) ("state the exact hypothesis tying `μ(Ask_j)/μ(Ask)` to `P(J = j)`")
Kind: N+ (the hypothesis of `sist_symmetric`, inhabited on a two-table Ask class)
Fidelity: exact
Hyps: (a) `w 0 = w 1` -/
theorem symmetric_tie (heq : w 0 = w 1) : ∀ T, askP T →
    pickMass (symData w hw hw1 ρ hρ c V r₀) askP recP symJ T *
        askMass (symData w hw hw1 ρ hρ c V r₀) askP =
      (symData w hw hw1 ρ hρ c V r₀).toPrior.stateMass T *
        recMass (symData w hw hw1 ρ hρ c V r₀) askP recP := by
  intro T hT
  rw [askMass_eq, recMass_eq]
  have h0 := stateMass_eq w hw hw1 ρ hρ c V r₀ 0
  have h1 := stateMass_eq w hw hw1 ρ hρ c V r₀ 1
  rw [fourState_zero] at h0
  rw [fourState_one] at h1
  rcases eq_four T with rfl | rfl | rfl | rfl
  · rw [pickMass_fAsk, h0, heq]; ring
  · rw [pickMass_fBoth, h1, ← heq]; ring
  · exact absurd hT not_askP_fRec
  · exact absurd hT not_askP_fOther

/-- **The class profile is `(1 + ρ)/2`** with equal positive Ask masses: the Ask-class average of
the brackets `1` (at `Ask₁`) and `ρ` (at `Ask₂`).
Source: bli-soto-b-2-006 (`ρ̄_i = ∑_j P(J = j)·[…]`); mandate §3.4
Kind: P
Fidelity: exact
Hyps: (a) `w 0 = w 1`, `0 < w 0` -/
theorem classProfile_eq (heq : w 0 = w 1) (hpos : 0 < w 0) :
    classProfile (symData w hw hw1 ρ hρ c V r₀).toPrior (univ.filter askP) fAsk true false =
      (1 + ρ) / 2 := by
  unfold classProfile
  rw [← askTerm_unit_eq_class, ← askMass_eq_classMass, askMass_eq]
  have h1 : askTerm (symData w hw hw1 ρ hρ c V r₀) askP fAsk (fun _ => 1) = w 0 + w 1 * ρ := by
    unfold askTerm
    rw [sum_base, Fintype.sum_prod_type]
    have hδ1 := pointCorr_ask w hw hw1 ρ hρ c V r₀
    have hδ2 := pointCorr_both w hw hw1 ρ hρ c V r₀
    simp only [state₀_eq, μ₀_eq, Fintype.sum_bool, Fin.sum_univ_four, fourState_zero,
      fourState_one, fourState_two, fourState_three, askP_fAsk, askP_fBoth, not_askP_fRec,
      not_askP_fOther, if_true, if_false, hδ1, hδ2]
    ring
  rw [h1, ← heq]
  field_simp
  ring

/-- **The symmetric verdict on the family** (the N+ of `sist_symmetric`, `ρ̄ ∈ (0, 1)`):
`EU Ask₁ give − EU Ask₁ refuse = (V·w(Rec) − c·(w(Ask₁) + w(Ask₂))) · (1 + ρ)/2 + w(Other)·Δr₀`.
Source: bli-soto-b-2-006; mandate T2(a); audit round 1 A1
Kind: N+ (`sist_symmetric` instantiated; the tie, `J`'s landing, positivity and the profile all
derived from the construction)
Fidelity: exact
Hyps: (a) `w 0 = w 1`, `0 < w 0`; does not use faith -/
theorem verdict (heq : w 0 = w 1) (hpos : 0 < w 0) :
    (symPrior w hw hw1 ρ hρ c V r₀).EU fAsk true - (symPrior w hw hw1 ρ hρ c V r₀).EU fAsk false =
      (V * w 2 - c * (w 0 + w 1)) * ((1 + ρ) / 2) + w 3 * (r₀ true - r₀ false) := by
  unfold symPrior
  rw [sist_symmetric (symData w hw hw1 ρ hρ c V r₀) askP recP symJ fAsk (fun _ b => r₀ b) V c
    (shaped w hw hw1 ρ hρ c V r₀) (by rw [massOf_point]; norm_num) (by rw [massOf_point]; norm_num)
    (hJ w hw hw1 ρ hρ c V r₀) (symmetric_tie w hw hw1 ρ hρ c V r₀ heq)
    (by rw [askMass_eq]; linarith [hw 1]),
    classProfile_eq w hw hw1 ρ hρ c V r₀ heq hpos, recMass_eq, askMass_eq, resTerm_eq]

/-- **The sign is `ρ`-free on the family** for every `ρ ∈ (−1, 1]` and an action-blind residual:
`give` is the one-step choice iff `c·μ(Ask) ≤ V·μ(Rec)`, strictly iff `<`
(`sist_sign_symmetric` instantiated at `ρ̄ = (1 + ρ)/2 > 0`).
Source: bli-soto-b-2-006 ("the verdict does not depend on how correlated the decisions are");
mandate T2(a) corollary
Kind: N+ (`sist_sign_symmetric` instantiated)
Fidelity: exact
Hyps: (a) `w 0 = w 1`, `0 < w 0`, `−1 < ρ`, `r₀ true = r₀ false`; does not use faith -/
theorem sign (heq : w 0 = w 1) (hpos : 0 < w 0) (hρ1 : -1 < ρ) (hr : r₀ true = r₀ false) :
    ((symPrior w hw hw1 ρ hρ c V r₀).IsOneStepChoice fAsk true ↔ c * (w 0 + w 1) ≤ V * w 2) ∧
      ((symPrior w hw hw1 ρ hρ c V r₀).EU fAsk false < (symPrior w hw hw1 ρ hρ c V r₀).EU fAsk true ↔
        c * (w 0 + w 1) < V * w 2) := by
  unfold symPrior
  have h := sist_sign_symmetric (symData w hw hw1 ρ hρ c V r₀) askP recP symJ fAsk
    (fun _ b => r₀ b) V c (shaped w hw hw1 ρ hρ c V r₀) (by rw [massOf_point]; norm_num)
    (by rw [massOf_point]; norm_num) (hJ w hw hw1 ρ hρ c V r₀)
    (symmetric_tie w hw hw1 ρ hρ c V r₀ heq) (by rw [askMass_eq]; linarith [hw 1])
    (by rw [classProfile_eq w hw hw1 ρ hρ c V r₀ heq hpos]; linarith)
    (by rw [resTerm_eq, hr]; ring)
  rw [recMass_eq, askMass_eq] at h
  exact h

/-- **`H_point` fails** on the family as soon as `Ask₂` has mass.
Source: bli-soto-a-2-013 (`H_point`); audit round 1 (the symmetric model's N+ is not the
pinned-Ask model's)
Kind: N−
Fidelity: exact
Hyps: (a) `0 < w 1` -/
theorem not_hPoint (h1 : 0 < w 1) : ¬ HPoint (symPrior w hw hw1 ρ hρ c V r₀) askP fAsk := by
  intro h
  have := h fBoth askP_fBoth fAsk_ne_fBoth.symm
  have h1' := stateMass_eq w hw hw1 ρ hρ c V r₀ 1
  rw [fourState_one] at h1'
  unfold symPrior at this
  rw [h1'] at this
  linarith

/-- **`H_unif` fails** on the family for `ρ < 1`: the policy disagreeing at the two Ask tables has
positive mass.
Source: bli-soto-a-2-013 (`H_unif`); audit round 1 (`sist_symmetric` was exercised only at
`ρ̄ = 1`)
Kind: N−
Fidelity: exact
Hyps: (a) `0 < w 0`, `ρ < 1` -/
theorem not_hUnif (hpos : 0 < w 0) (hρ1 : ρ < 1) :
    ¬ HUnif (symPrior w hw hw1 ρ hρ c V r₀) askP fAsk := by
  intro h
  let k : K := (true, false, false, false)
  have hμ : 0 < (symPrior w hw hw1 ρ hρ c V r₀).μ ((0, false), smk k) := by
    change 0 < (symData w hw hw1 ρ hρ c V r₀).μ₀ (0, false) * pushLaw smk (sg ρ) (smk k)
    apply mul_pos
    · simp only [μ₀_eq]; positivity
    · have hle : sg ρ k ≤ pushLaw smk (sg ρ) (smk k) := by
        unfold pushLaw
        have := Finset.single_le_sum (f := fun k' => if smk k' = smk k then sg ρ k' else 0)
          (fun k' _ => by split_ifs; exact sg_nonneg hρ k'; exact le_rfl)
          (Finset.mem_univ k)
        simpa using this
      have : 0 < sg ρ k := by
        unfold sg pairρ
        simp [k]
        linarith
      linarith
  have := h _ hμ fBoth askP_fBoth
  change smk k fBoth = smk k fAsk at this
  simp [k] at this

/-! ## The instance at `ρ = 1/2` -/

/-- The masses `(49/200, 49/200, 49/100, 2/100)`: the source's `49 % / 49 % / 2 %` with the Ask
mass split over two tables.
Source: bli-slides-034 (the proportions); mandate T2(c)
Kind: D
Fidelity: exact -/
def wHalf : Fin 4 → ℚ
  | 0 => 49 / 200
  | 1 => 49 / 200
  | 2 => 49 / 100
  | 3 => 2 / 100

/-- `wHalf ≥ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wHalf_nonneg : ∀ s, 0 ≤ wHalf s := by intro s; fin_cases s <;> norm_num [wHalf]

/-- `∑ wHalf = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wHalf_sum : ∑ s, wHalf s = 1 := by rw [Fin.sum_univ_four]; norm_num [wHalf]

/-- `|1/2| ≤ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma half_abs : |(1 / 2 : ℚ)| ≤ 1 := by rw [abs_of_nonneg (by norm_num)]; norm_num

/-- **The instance at `ρ = 1/2`**, masses `(49/200, 49/200, 49/100, 2/100)`, `(100, 10)`, any
residual `|r₀| ≤ 10`: the profile is `ρ̄ = 3/4` (strictly between `0` and `1`), the difference is
`1323/40 + (2/100)·(r₀ give − r₀ refuse)`, and the one-step rule pays strictly.
Source: bli-soto-b-2-006; mandate T2(a), (c); audit round 1 A1
Kind: N+
Fidelity: exact
Hyps: (a) `|r₀| ≤ 10` -/
theorem instance_half (r₀ : Bool → ℚ) (hr : ∀ a, |r₀ a| ≤ 10) :
    classProfile (symData wHalf wHalf_nonneg wHalf_sum (1 / 2) half_abs 10 100 r₀).toPrior
        (univ.filter askP) fAsk true false = 3 / 4 ∧
      (symPrior wHalf wHalf_nonneg wHalf_sum (1 / 2) half_abs 10 100 r₀).EU fAsk true -
          (symPrior wHalf wHalf_nonneg wHalf_sum (1 / 2) half_abs 10 100 r₀).EU fAsk false =
        1323 / 40 + 2 / 100 * (r₀ true - r₀ false) ∧
      (symPrior wHalf wHalf_nonneg wHalf_sum (1 / 2) half_abs 10 100 r₀).IsOneStepChoice fAsk true ∧
      (symPrior wHalf wHalf_nonneg wHalf_sum (1 / 2) half_abs 10 100 r₀).EU fAsk false <
        (symPrior wHalf wHalf_nonneg wHalf_sum (1 / 2) half_abs 10 100 r₀).EU fAsk true := by
  have heq : wHalf 0 = wHalf 1 := by simp [wHalf]
  have hpos : 0 < wHalf 0 := by norm_num [wHalf]
  have hcp := classProfile_eq wHalf wHalf_nonneg wHalf_sum (1 / 2) half_abs 10 100 r₀ heq hpos
  have hv := verdict wHalf wHalf_nonneg wHalf_sum (1 / 2) half_abs 10 100 r₀ heq hpos
  have hv' : (symPrior wHalf wHalf_nonneg wHalf_sum (1 / 2) half_abs 10 100 r₀).EU fAsk true -
      (symPrior wHalf wHalf_nonneg wHalf_sum (1 / 2) half_abs 10 100 r₀).EU fAsk false =
        1323 / 40 + 2 / 100 * (r₀ true - r₀ false) := by
    rw [hv]; simp only [wHalf]; ring
  have ht := abs_le.mp (hr true)
  have hf := abs_le.mp (hr false)
  refine ⟨by rw [hcp]; norm_num, hv', fun b => ?_, by linarith⟩
  cases b
  · linarith
  · exact le_rfl

end Sym2

end Cleanroom.Bli.UdtBliSist
