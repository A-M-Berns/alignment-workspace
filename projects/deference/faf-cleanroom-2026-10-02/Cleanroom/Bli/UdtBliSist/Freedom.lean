import Cleanroom.Bli.UdtBliSist.Skeleton
import Cleanroom.Bli.UdtBliSist.SistWitness

/-!
# `udt-bli-sist` · Freedom: freedom of action — the `ρ`-threshold at Rec (T4, U7)

**The prior** `freedomPrior w ρ c V` over `udt-bli-core`'s `mugTables` (`Ask`, `Rec`, `Other`):
masses `w`, and a policy law on the three points that is the pushforward of
`(a, r, o) ↦ pairρ ρ a r · 1/2` — the Ask and Rec points agree with probability `(1+ρ)/2` and
disagree with probability `(1−ρ)/2`, the Other point is independent uniform; `ρ ∈ [−1, 1]`.
Utility (bli-soto-b-2-015's F2, "paying in Rec costs"): Ask: `−c·[pp·Ask = give]`;
Rec: `V·[pp·Ask = give] − c·[pp·Rec = give]` (utilities add, journal l. 636); Other: `0`.

* `EU_rec_diff`: `EU Rec give − EU Rec refuse = w(Rec)·(V·ρ − c) − w(Ask)·c·ρ`;
* `EU_ask_diff`: `EU Ask give − EU Ask refuse = w(Rec)·(V − c·ρ) − w(Ask)·c`;
* `refuse_rec_iff`: refuse at Rec (strictly) iff `ρ·(V·w(Rec) − c·w(Ask)) < c·w(Rec)` — the general-mass
  form; with equal masses, iff `ρ < c/(V − c)` (`refuse_rec_iff_eq`), which is `1/9` at `(100, 10)`
  (`refuse_rec_iff_eq_100_10`): an exact rational root;
* `pay_ask`: pay at Ask (strictly) for every `ρ ∈ [−1, 1]` whenever `2c < V` (equal masses);
* `ρ = 0`: `independentPoints_zero` (the points are independent), pay at Ask and refuse at Rec —
  Abram's claim; `ρ = 1`: pay at both (`pay_both_one`) — Soto's "losing money senselessly" with the
  net `V − 2c > 0`.
* **F1** (the Rec action ignored): `EU_rec_diff_F1 = (V·w(Rec) − c·w(Ask))·ρ`: at Rec every action
  ties **only for independent points**; with `ρ ≠ 0` the Rec point acts through its correlation with
  the Ask point (finding F12).

Sources: bli-soto-b-2-015, bli-soto-a-090 (the independent-points claim), journal ll. 627–637,
mandate T4.
-/

namespace Cleanroom.Bli.UdtBliSist

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliCore.Mugging Finset

/-! ## Integrals under a pushforward law -/

section PushInt

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [Fintype A] [DecidableEq A]
variable {K : Type} [Fintype K] (mk : K → Policy 𝒟 A) (g : K → ℚ)

/-- Integrals against a pushforward law are sums over the parameters.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_pushLaw_mul (F : Policy 𝒟 A → Prop) [DecidablePred F] (h : Policy 𝒟 A → ℚ) :
    (∑ π, if F π then pushLaw mk g π * h π else 0) =
      ∑ k, if F (mk k) then g k * h (mk k) else 0 := by
  unfold pushLaw
  have e : ∀ π, (if F π then (∑ k, if mk k = π then g k else 0) * h π else 0) =
      ∑ k, if mk k = π ∧ F π then g k * h π else 0 := by
    intro π
    split_ifs with hF
    · rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp_all
    · simp [hF]
  simp only [e]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_eq_single (mk k)]
  · simp
  · intro π _ hπ
    simp [Ne.symm hπ]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The one-step value under a pushforward policy law**, as a ratio of parameter sums.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma EU_push (D : IndepData 𝒮 m 𝒟 A) (hν : D.ν = pushLaw mk g) (T : ↥𝒟) (a : A) :
    D.toPrior.EU T a =
      (∑ ω₀, D.μ₀ ω₀ * ∑ k, if mk k T = a then g k * D.U₀ ω₀ (mk k) else 0) /
        ∑ k, if mk k T = a then g k else 0 := by
  unfold FiniteBLIPrior.EU condExp
  change D.toPrior.ppUtil T a / D.toPrior.ppMass T a = _
  rw [D.ppUtil_toPrior, D.ppMass_toPrior, hν, massOf_pushLaw]
  congr 1
  apply Finset.sum_congr rfl
  intro ω₀ _
  congr 1
  exact sum_pushLaw_mul mk g (fun π => π T = a) (D.U₀ ω₀)

end PushInt

namespace Freedom

/-! ## The correlated law on the three points -/

/-- The joint law of the Ask and Rec points: agree with probability `(1+ρ)/2`, disagree with
`(1−ρ)/2`, in four cells of `(1±ρ)/4`.
Source: mandate T4 (`ν(gg) = ν(rr) = (1+ρ)/4`, `ν(gr) = ν(rg) = (1−ρ)/4`)
Kind: D
Fidelity: exact -/
def pairρ (ρ : ℚ) (a r : Bool) : ℚ := if a = r then (1 + ρ) / 4 else (1 - ρ) / 4

/-- The policy with the given values at `Ask`, `Rec`, `Other`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def fmk (k : Bool × Bool × Bool) : Policy mugTables Bool :=
  fun T => if T = askT then k.1 else if T = recT then k.2.1 else k.2.2

/-- The weights: the pair law on `(Ask, Rec)` times uniform on `Other`.
Source: mandate T4
Kind: D
Fidelity: exact -/
def fg (ρ : ℚ) (k : Bool × Bool × Bool) : ℚ := pairρ ρ k.1 k.2.1 * (1 / 2)

/-- `fmk k Ask = k.1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma fmk_askT (k : Bool × Bool × Bool) : fmk k askT = k.1 := by simp [fmk]

/-- `fmk k Rec = k.2.1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma fmk_recT (k : Bool × Bool × Bool) : fmk k recT = k.2.1 := by
  simp [fmk, askT_ne_recT.symm]

/-- `fmk k Other = k.2.2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma fmk_otherT (k : Bool × Bool × Bool) : fmk k otherT = k.2.2 := by
  simp [fmk, askT_ne_otherT.symm, recT_ne_otherT.symm]

/-- `fg ≥ 0` for `|ρ| ≤ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fg_nonneg {ρ : ℚ} (hρ : |ρ| ≤ 1) (k : Bool × Bool × Bool) : 0 ≤ fg ρ k := by
  have h := abs_le.mp hρ
  unfold fg pairρ
  split_ifs <;> linarith

/-- `∑ fg = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_fg (ρ : ℚ) : ∑ k : Bool × Bool × Bool, fg ρ k = 1 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, fg, pairρ]
  simp
  ring

/-- **The freedom-of-action utility** (F2): Ask: `−c·[pp·Ask = give]`; Rec:
`V·[pp·Ask = give] − c·[pp·Rec = give]`; Other: `0`.
Source: bli-soto-b-2-015 (F2: "if `Rec(Q_m)` is the case, the action is not ignored, and paying
indeed leads to losing that amount of money"); journal l. 636 (utilities add)
Kind: D
Fidelity: exact -/
def fU (c V : ℚ) (s : Fin 3) (π : Policy mugTables Bool) : ℚ :=
  if s = 0 then -c * ind (π askT) else if s = 1 then V * ind (π askT) - c * ind (π recT) else 0

/-- **F1's utility** (the Rec action ignored): Rec: `V·[pp·Ask = give]`.
Source: bli-soto-b-2-015 (F1: "this action is completely ignored")
Kind: D
Fidelity: exact -/
def fU1 (c V : ℚ) (s : Fin 3) (π : Policy mugTables Bool) : ℚ :=
  if s = 0 then -c * ind (π askT) else if s = 1 then V * ind (π askT) else 0

variable (w : Fin 3 → ℚ) (hw : ∀ s, 0 ≤ w s) (hw1 : ∑ s, w s = 1) (ρ : ℚ) (hρ : |ρ| ≤ 1) (c V : ℚ)

/-- **The freedom-of-action data**: masses `w`, the correlated law at `ρ`, the F2 utility.
Source: bli-soto-b-2-015; mandate T4
Kind: D
Fidelity: exact -/
def freedomData : IndepData witIndex 1 mugTables Bool where
  Ω₀ := Fin 3
  μ₀ := w
  μ₀_nonneg := hw
  μ₀_sum_one := hw1
  state₀ := mugState
  small₀ := fun s φ => decide ((mugState s).1 φ = 1)
  faith₀ := faith_of_zeroOne w mugState mug_zeroOne
  ν := pushLaw fmk (fg ρ)
  ν_nonneg := pushLaw_nonneg _ _ (fg_nonneg hρ)
  ν_sum_one := by rw [sum_pushLaw, sum_fg]
  U₀ := fU c V

/-- **The freedom-of-action prior** (definition of record, T4).
Source: bli-soto-b-2-015; mandate T4
Kind: D
Fidelity: exact -/
def freedomPrior : FiniteBLIPrior witIndex 1 mugTables Bool := (freedomData w hw hw1 ρ hρ c V).toPrior

/-- The F1 variant of the data (the Rec action ignored).
Source: bli-soto-b-2-015 (F1)
Kind: D
Fidelity: exact -/
def freedomData1 : IndepData witIndex 1 mugTables Bool :=
  { freedomData w hw hw1 ρ hρ c V with U₀ := fU1 c V }

/-- The F1 prior.
Source: bli-soto-b-2-015 (F1)
Kind: D
Fidelity: exact -/
def freedomPrior1 : FiniteBLIPrior witIndex 1 mugTables Bool :=
  (freedomData1 w hw hw1 ρ hρ c V).toPrior

/-- **The exact identity at Rec**: `EU Rec give − EU Rec refuse = w(Rec)·(V·ρ − c) − w(Ask)·c·ρ`.
Source: bli-soto-b-2-015; mandate T4 ("the exact identities")
Kind: P
Fidelity: exact
Hyps: (a) none (`|ρ| ≤ 1` is the law's well-formedness); does not use faith -/
theorem EU_rec_diff :
    (freedomPrior w hw hw1 ρ hρ c V).EU recT true - (freedomPrior w hw hw1 ρ hρ c V).EU recT false =
      w 1 * (V * ρ - c) - w 0 * c * ρ := by
  unfold freedomPrior
  rw [EU_push fmk (fg ρ) _ rfl, EU_push fmk (fg ρ) _ rfl]
  change (∑ s : Fin 3, w s * ∑ k, if fmk k recT = true then fg ρ k * fU c V s (fmk k) else 0) /
      (∑ k, if fmk k recT = true then fg ρ k else 0) -
    (∑ s : Fin 3, w s * ∑ k, if fmk k recT = false then fg ρ k * fU c V s (fmk k) else 0) /
      (∑ k, if fmk k recT = false then fg ρ k else 0) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three, fmk_askT, fmk_recT,
    fmk_otherT, fU, fg, pairρ]
  simp
  ring

/-- **The exact identity at Ask**: `EU Ask give − EU Ask refuse = w(Rec)·(V − c·ρ) − w(Ask)·c`.
Source: bli-soto-b-2-015; mandate T4
Kind: P
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem EU_ask_diff :
    (freedomPrior w hw hw1 ρ hρ c V).EU askT true - (freedomPrior w hw hw1 ρ hρ c V).EU askT false =
      w 1 * (V - c * ρ) - w 0 * c := by
  unfold freedomPrior
  rw [EU_push fmk (fg ρ) _ rfl, EU_push fmk (fg ρ) _ rfl]
  change (∑ s : Fin 3, w s * ∑ k, if fmk k askT = true then fg ρ k * fU c V s (fmk k) else 0) /
      (∑ k, if fmk k askT = true then fg ρ k else 0) -
    (∑ s : Fin 3, w s * ∑ k, if fmk k askT = false then fg ρ k * fU c V s (fmk k) else 0) /
      (∑ k, if fmk k askT = false then fg ρ k else 0) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three, fmk_askT, fmk_recT,
    fmk_otherT, fU, fg, pairρ]
  simp
  ring

/-- **F1: the Rec difference when the Rec action is ignored** is `(V·w(Rec) − c·w(Ask))·ρ`: the
actions at Rec tie **iff `ρ = 0`** (or the stakes balance). With correlated points the Rec point
still moves the Ask point's conditional law, so "the choice is ignored in Rec" does not make the
Rec choice indifferent.
Source: bli-soto-b-2-015 (F1: "SIST works as stated"); mandate T4 ("at Rec every action ties") —
corrected: finding F12
Kind: P
Fidelity: exact (the source's "ties" is the `ρ = 0` instance)
Hyps: (a) none; does not use faith -/
theorem EU_rec_diff_F1 :
    (freedomPrior1 w hw hw1 ρ hρ c V).EU recT true -
        (freedomPrior1 w hw hw1 ρ hρ c V).EU recT false =
      (V * w 1 - c * w 0) * ρ := by
  unfold freedomPrior1 freedomData1
  rw [EU_push fmk (fg ρ) _ rfl, EU_push fmk (fg ρ) _ rfl]
  change (∑ s : Fin 3, w s * ∑ k, if fmk k recT = true then fg ρ k * fU1 c V s (fmk k) else 0) /
      (∑ k, if fmk k recT = true then fg ρ k else 0) -
    (∑ s : Fin 3, w s * ∑ k, if fmk k recT = false then fg ρ k * fU1 c V s (fmk k) else 0) /
      (∑ k, if fmk k recT = false then fg ρ k else 0) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three, fmk_askT, fmk_recT,
    fmk_otherT, fU1, fg, pairρ]
  simp
  ring

/-! ## Corollaries -/

/-- **Refuse at Rec, general masses**: the one-step rule strictly refuses at Rec iff
`ρ·(V·w(Rec) − c·w(Ask)) < c·w(Rec)`, and `refuse` is a one-step choice iff `≤`.
Source: bli-soto-b-2-015 ("the one-step verdict at Rec-states as a function of `ρ`"); mandate T4
(the general-mass form is the statement)
Kind: P
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem refuse_rec_iff :
    ((freedomPrior w hw hw1 ρ hρ c V).EU recT true < (freedomPrior w hw hw1 ρ hρ c V).EU recT false ↔
      ρ * (V * w 1 - c * w 0) < c * w 1) ∧
    ((freedomPrior w hw hw1 ρ hρ c V).IsOneStepChoice recT false ↔
      ρ * (V * w 1 - c * w 0) ≤ c * w 1) := by
  have hd := EU_rec_diff w hw hw1 ρ hρ c V
  constructor
  · constructor <;> intro h <;> nlinarith
  · unfold FiniteBLIPrior.IsOneStepChoice
    constructor
    · intro h
      have := h true
      nlinarith
    · intro h b
      cases b
      · exact le_rfl
      · nlinarith

/-- **The threshold with equal masses**: with `w(Ask) = w(Rec) = w > 0` and `c < V`, the one-step
rule strictly refuses at Rec iff `ρ < c / (V − c)`.
Source: bli-soto-b-2-015 ("refuse for `ρ` below a threshold"); mandate T4
Kind: P
Fidelity: exact (an exact rational root)
Hyps: (a) `w 0 = w 1`, `0 < w 1`, `c < V`; does not use faith -/
theorem refuse_rec_iff_eq (heq : w 0 = w 1) (hpos : 0 < w 1) (hV : c < V) :
    (freedomPrior w hw hw1 ρ hρ c V).EU recT true < (freedomPrior w hw hw1 ρ hρ c V).EU recT false ↔
      ρ < c / (V - c) := by
  rw [(refuse_rec_iff w hw hw1 ρ hρ c V).1, heq, lt_div_iff₀ (by linarith)]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **The threshold at `(100, 10)` is `1/9`.**
Source: mandate T4 ("`= 1/9` at `(100, 10)`")
Kind: P
Fidelity: exact
Hyps: (a) `w 0 = w 1`, `0 < w 1`; does not use faith -/
theorem refuse_rec_iff_eq_100_10 (heq : w 0 = w 1) (hpos : 0 < w 1) :
    (freedomPrior w hw hw1 ρ hρ 10 100).EU recT true <
        (freedomPrior w hw hw1 ρ hρ 10 100).EU recT false ↔ ρ < 1 / 9 := by
  rw [refuse_rec_iff_eq w hw hw1 ρ hρ 10 100 heq hpos (by norm_num)]
  norm_num

/-- **Pay at Ask for every `ρ ∈ [−1, 1]`** with equal masses, `0 ≤ c` and `2c < V`.
Source: bli-soto-b-2-015; mandate T4 ("pays at Ask for every `ρ ∈ [−1, 1]`")
Kind: P
Fidelity: exact
Hyps: (a) `w 0 = w 1`, `0 < w 1`, `0 ≤ c`, `2c < V`; does not use faith -/
theorem pay_ask (heq : w 0 = w 1) (hpos : 0 < w 1) (hc : 0 ≤ c) (hV : 2 * c < V) :
    (freedomPrior w hw hw1 ρ hρ c V).EU askT false < (freedomPrior w hw hw1 ρ hρ c V).EU askT true ∧
      (freedomPrior w hw hw1 ρ hρ c V).IsOneStepChoice askT true := by
  have hd := EU_ask_diff w hw hw1 ρ hρ c V
  have h := abs_le.mp hρ
  have hkey : 0 < w 1 * (V - c * ρ) - w 0 * c := by
    rw [heq]
    have : 0 < V - c * ρ - c := by nlinarith
    nlinarith
  refine ⟨by linarith, fun b => ?_⟩
  cases b
  · linarith
  · exact le_rfl

/-- **`ρ = 0`: the points are independent** (`IndependentPoints`).
Source: bli-soto-a-090 ("if `P` sees give/refuse in Ask and Rec branches as independent policy
points"); mandate T4
Kind: P
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem independentPoints_zero : (freedomPrior w hw hw1 0 (by norm_num) c V).IndependentPoints := by
  intro T T' a b hne
  unfold freedomPrior
  rw [IndepData.pairMass_toPrior, IndepData.ppMass_toPrior, IndepData.ppMass_toPrior]
  change massOf (pushLaw fmk (fg 0)) (fun π => π T = a ∧ π T' = b) =
    massOf (pushLaw fmk (fg 0)) (fun π => π T = a) * massOf (pushLaw fmk (fg 0)) (fun π => π T' = b)
  rw [massOf_pushLaw, massOf_pushLaw, massOf_pushLaw]
  rcases Sist3.eq_three T with rfl | rfl | rfl <;> rcases Sist3.eq_three T' with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hne
    | (simp only [Fintype.sum_prod_type, Fintype.sum_bool, fmk_askT, fmk_recT, fmk_otherT, fg, pairρ]
       cases a <;> cases b <;> simp <;> norm_num)

/-- **`ρ = 0`: pay at Ask, refuse at Rec** (Abram's claim) with equal masses, `0 < c`, `2c < V`.
Source: bli-soto-a-090 ("UDT gives in Ask and not in Rec"); mandate T4
Kind: P
Fidelity: exact
Hyps: (a) `w 0 = w 1`, `0 < w 1`, `0 < c`, `2c < V`; does not use faith -/
theorem abram_zero (heq : w 0 = w 1) (hpos : 0 < w 1) (hc : 0 < c) (hV : 2 * c < V) :
    (freedomPrior w hw hw1 0 (by norm_num) c V).EU askT false <
        (freedomPrior w hw hw1 0 (by norm_num) c V).EU askT true ∧
      (freedomPrior w hw hw1 0 (by norm_num) c V).EU recT true <
        (freedomPrior w hw hw1 0 (by norm_num) c V).EU recT false := by
  refine ⟨(pay_ask w hw hw1 0 (by norm_num) c V heq hpos (le_of_lt hc) hV).1, ?_⟩
  rw [(refuse_rec_iff w hw hw1 0 (by norm_num) c V).1]
  nlinarith

/-- **`ρ = 1`: pay at both** (Soto's "losing money senselessly") with equal masses and `2c < V`:
the net at Rec is `w·(V − 2c) > 0`.
Source: bli-soto-b-2-015 ("it either pays everywhere … if `100 − 10 − 10 > 0`"); mandate T4
Kind: P
Fidelity: exact
Hyps: (a) `w 0 = w 1`, `0 < w 1`, `0 ≤ c`, `2c < V`; does not use faith -/
theorem pay_both_one (heq : w 0 = w 1) (hpos : 0 < w 1) (hc : 0 ≤ c) (hV : 2 * c < V) :
    (freedomPrior w hw hw1 1 (by norm_num) c V).EU askT false <
        (freedomPrior w hw hw1 1 (by norm_num) c V).EU askT true ∧
      (freedomPrior w hw hw1 1 (by norm_num) c V).EU recT false <
        (freedomPrior w hw hw1 1 (by norm_num) c V).EU recT true ∧
      (freedomPrior w hw hw1 1 (by norm_num) c V).EU recT true -
        (freedomPrior w hw hw1 1 (by norm_num) c V).EU recT false = w 1 * (V - 2 * c) := by
  have hd := EU_rec_diff w hw hw1 1 (by norm_num) c V
  rw [heq] at hd
  refine ⟨(pay_ask w hw hw1 1 (by norm_num) c V heq hpos hc hV).1, ?_, ?_⟩
  · nlinarith
  · rw [hd]; ring

end Freedom

end Cleanroom.Bli.UdtBliSist
