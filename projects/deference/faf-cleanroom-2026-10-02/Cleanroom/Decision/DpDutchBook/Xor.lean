import Cleanroom.Decision.DpDutchBook.NewcombSeed
import Cleanroom.Decision.DpCalibration.Theories

/-!
# T13: XOR blackmail under both semantics — the evaluators, the policy values, implementability

**The tree** (P06.md line 7; `xorTree δ c X`): `D ∼ Bern(δ)` (chance index `0` = termites);
a hypothetical query of `d_L` (the predictor's simulation, answer `x`); the letter is sent iff
exactly one of `{D = 1, x = pay}`; on letter runs the real query (answer `a`);
`r = −c·[a = pay] − X·[D = 1]`; worlds `(D, x, L, a?)` with `a? = none` off the letter. The
observation is `O_L = {L = 1}`; action events read the live act. Encoding: one shape on every
branch — the live node is present on every run and its draw is recorded (and paid) only on
letter runs (disclosed on `xorTree`; nothing conditioned on `L = 1` sees the difference).
`q := C(d_L)(pay)`, `ν_L := δ(1−q) + (1−δ)q`.

* **Definition 6** (`xor_nu_pay_L`, `xorE_pay`, `xorE_refuse`, `xorE_sub`, `xor_disaster_same`,
  `xor_lie_given_L`, `xor_lie_given_pay`): `ν(pay ∧ L) = q·ν_L` (F3′ at the real node), the
  disaster conditional `P(D = 1 ∣ L, a) = δ(1−q)/ν_L` is the same for both acts, so conditioning
  refuses by exactly `c`; the letter is false on letter runs w.p. `q(1−q)/ν_L` and on pay runs
  w.p. `δ(1−q)/ν_L` (= the disaster conditional); **R1-state pays** with margin `X − c`
  (`xorR1State_pay`, `_refuse`); **R3 = conditioning** at every label (`xorR3_pay/_refuse`,
  via `r3Val_eq_qSum_div` under F3′ structural, `xor_actRecordingStruct` — a second inhabitant
  of T7's hypothesis package with `O_d ≠ ⊤`, standing hypothesis `ν_L(m) > 0` for `0 < δ < 1`).
* **Policy values** under both semantics: `V(pay) = −Xδ − c(1−δ)`, `V(refuse) = −Xδ`
  (`xor_policy_values`, `xor_policy_values'`; `−10990` vs `−10000` at the L–S numbers).
* **6′** (`xorE'_pay`, `xorE'_refuse`, `xor_value'`, `xorDoCdt'`, `xor_forecast`): the seed
  makes `a = x`, so `e'(pay) = −c`, `e'(refuse) = −X` — evidential choice **pays** by `X − c`;
  the shared-seed value `−δX − (1−δ)cq` is affine in `q` (no mixed label is forced); the
  deviation evaluator refuses by `(1−δ)c` and the do-CDT construal by `c`; a deterministic
  refuser receiving the letter forecasts disaster with certainty under Definition 6 (`q = 0`),
  while at `q = ½` the forecast is `δ`.
* **Implementability** (T13(d)): `ImplementableSeed` — the act is independent of every
  structurally pre-query event on `O_d`-runs under 6′; **XOR fails it** (`xor_not_implementableSeed`:
  `ν'(pay ∣ D = 1, L) = 0` against `q`), while under Definition 6 the same identities hold
  (`xor_implementable_def6_D`). The ⇐ direction is the OPEN row `implementable_of_almostFair_open`
  (the almost-fair case of P06-11′'s "path-irrelevant nesting"; the general clause is not defined
  here — see the report).

Not done: Theorem 1's `fiberForced` evaluator on this tree (attempted; see the report), the
masked/limit grades under 6′, UDT with disposition events (T13(f)), the fallible predictor (T13(e)).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpDutchBook

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-- XOR worlds `(D, x, L, a?)`: termites, the predictor's sample, the letter, the live act (`none`
off the letter). Source: P06.md line 7 ("worlds carry `(D, x, L, a)`"). Kind: D -/
abbrev XorW : Type := Bool × Act2 × Bool × Option Act2

/-- Termites at chance index `i`: index `0` = termites. Source: P06.md line 7. Kind: D -/
def xorTermites (i : Fin 2) : Bool := if i = 0 then true else false

/-- The letter is sent iff exactly one of `{D = 1, x = pay}`. Source: P06.md line 7. Kind: D -/
def xorLetter : Bool → Act2 → Bool
  | true, .a => false
  | true, .b => true
  | false, .a => true
  | false, .b => false

/-- The leaf world `(D, x, L, a?)`: the live draw is recorded only on letter runs.
Source: P06.md line 7 ("worlds carry `(D, x, L, a)`"). Kind: D -/
def xorWorld (D : Bool) (x a : Act2) : XorW :=
  (D, x, xorLetter D x, if xorLetter D x = true then some a else none)

/-- The payoff `−c·[letter ∧ a = pay] − X·[D = 1]`. Source: P06.md line 7. Kind: D -/
def xorPayW (c X : ℚ) (D : Bool) (x a : Act2) : ℚ :=
  -(if xorLetter D x = true ∧ a = .a then c else 0) - (if D = true then X else 0)

/-- **XOR blackmail** `xorTree δ c X`: termites, the predictor's simulation, the live query.
Source: P06.md line 7; dp-sl-054; mandate T13
Kind: D
Fidelity: variant: the live node is present on every run and its draw is recorded (and paid)
only on letter runs — off the letter the source does not query the agent; the extra draw is
payoff- and world-irrelevant there and `O_L = {L = 1}` excludes those runs from every
conditional, so no headline quantity is affected (the one-shape encoding keeps the leaves
uniform, as `opaqueNewcomb`'s) -/
def xorTree (δ : ℚ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (c X : ℚ) : Tree XorW Unit (fun _ => Act2) ℚ :=
  .chance 2 (FinDistr.coin δ h0 h1) fun i =>
    .decision () fun x =>
      .decision () fun a =>
        .leaf (xorWorld (xorTermites i) x a) (xorPayW c X (xorTermites i) x a)

/-- `O_{d_L} = {L = 1}`. Source: P06.md line 7. Kind: D -/
def xorObs : Unit → Finset XorW := fun _ => Finset.univ.filter fun w => w.2.2.1 = true

/-- Action events: the live act. Source: P06.md line 7. Kind: D -/
def xorActEv : (d : Unit) → Act2 → Finset XorW
  | _, a => Finset.univ.filter fun w => w.2.2.2 = some a

/-- The event "termites". Source: none: infrastructure. Kind: D -/
def xorD : Finset XorW := Finset.univ.filter fun w => w.1 = true

/-- The event "no termites". Source: none: infrastructure. Kind: D -/
def xorNotD : Finset XorW := Finset.univ.filter fun w => w.1 = false

/-- The event "the letter's claim is false": on a letter run, `D = [a = pay]` (the claim is
"exactly one of termites and paying"). Source: P06-1′ ("the letter's claim is false on a letter
run exactly when the live draw differs from the simulation's"). Kind: D -/
def xorLie : Finset XorW :=
  Finset.univ.filter fun w => w.2.2.1 = true ∧ w.1 = decide (w.2.2.2 = some Act2.a)

section tree

variable (δ : ℚ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (c X : ℚ) (C : Proc Unit (fun _ => Act2) ℚ)

/-- Sums over the eight leaves. Source: none: infrastructure. Kind: L -/
theorem xorTree_sum {M : Type} [AddCommMonoid M] (f : (xorTree δ h0 h1 c X).Leaves → M) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ x : Act2, ∑ a : Act2, f ⟨i, ⟨x, ⟨a, ()⟩⟩⟩ := by
  unfold xorTree at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- `ν_L := δ(1−q) + (1−δ)q`, the letter's probability. Source: P06-1′. Kind: D -/
def xorNuL (q : ℚ) : ℚ := δ * (1 - q) + (1 - δ) * q

/-- `ν(L = 1) = ν_L`. Source: none: infrastructure. Kind: L -/
theorem xor_nu_L : nu C (xorTree δ h0 h1 c X) (xorObs ()) = xorNuL δ ((C ()).w .a) := by
  rw [nu_eq_sum, xorTree_sum]
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  simp [Act2.sum_univ, xorTree, xorWorld, xorPayW, xorLetter, xorTermites, Fin.sum_univ_two, xorObs, FinDistr.coin]
  unfold xorNuL; rw [hb]; ring

/-- **`ν(a ∧ L) = C(d_L)(a)·ν_L`** — F3′ at the real node: self-transparency survives the nested
fiber. Source: P06.md line 7 ("F3′ holds at the real node under Def 6 (self-transparency
`ν(pay ∣ L=1) = q` survives)"); mandate T13(a). Kind: P. Fidelity: exact -/
theorem xor_nu_act_L (a : Act2) :
    nu C (xorTree δ h0 h1 c X) (xorActEv () a ∩ xorObs ()) = (C ()).w a * xorNuL δ ((C ()).w .a) := by
  rw [nu_eq_sum, xorTree_sum]
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  cases a <;>
    simp [Act2.sum_univ, xorTree, xorWorld, xorPayW, xorLetter, xorTermites, Fin.sum_univ_two, xorObs, xorActEv,
      FinDistr.coin] <;>
    unfold xorNuL <;> rw [hb] <;> ring

/-- `ν(D ∧ a ∧ L) = δ(1−q)·C(d_L)(a)`. Source: none: infrastructure. Kind: L -/
theorem xor_nu_D_act_L (a : Act2) :
    nu C (xorTree δ h0 h1 c X) (xorD ∩ xorActEv () a ∩ xorObs ()) =
      δ * (1 - (C ()).w .a) * (C ()).w a := by
  rw [nu_eq_sum, xorTree_sum]
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  cases a <;>
    simp [Act2.sum_univ, xorTree, xorWorld, xorPayW, xorLetter, xorTermites, Fin.sum_univ_two, xorObs, xorActEv, xorD,
      FinDistr.coin] <;>
    rw [hb] <;> ring

/-- `𝔼[r · 1_{a ∧ L}]`. Source: none: infrastructure. Kind: L -/
theorem xor_paySum_act_L (a : Act2) :
    paySum C (xorTree δ h0 h1 c X) (xorActEv () a ∩ xorObs ()) =
      (C ()).w a * (δ * (1 - (C ()).w .a) * (-(if a = .a then c else 0) - X) +
        (1 - δ) * (C ()).w .a * (-(if a = .a then c else 0))) := by
  rw [paySum_eq_sum_ite, xorTree_sum]
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  cases a <;>
    simp [Act2.sum_univ, xorTree, xorWorld, xorPayW, xorLetter, xorTermites, Fin.sum_univ_two, xorObs, xorActEv,
      FinDistr.coin] <;>
    rw [hb] <;> ring

/-- The strictly calibrated act value at the letter point `e(a) = 𝔼[r ∣ a ∧ L]`.
Source: P06.md vocabulary ("EV = Jeffrey news value at the strictly observation-calibrated state").
Kind: D -/
noncomputable def xorE (a : Act2) : ℚ := condExp C (xorTree δ h0 h1 c X) (xorActEv () a ∩ xorObs ())

/-- **`e(pay) = −c − X·δ(1−q)/ν_L`** at `0 < q`, `ν_L > 0`.
Source: dp-sl-054; mandate T13(a). Kind: P. Fidelity: exact. Hyps: (a) `0 < q`, `0 < ν_L` -/
theorem xorE_pay (hq : 0 < (C ()).w .a) (hL : 0 < xorNuL δ ((C ()).w .a)) :
    xorE δ h0 h1 c X C .a = -c - X * (δ * (1 - (C ()).w .a) / xorNuL δ ((C ()).w .a)) := by
  unfold xorE condExp
  rw [xor_paySum_act_L, xor_nu_act_L]
  simp only [eq_self_iff_true, if_true]
  have hne : xorNuL δ ((C ()).w .a) ≠ 0 := hL.ne'
  rw [div_eq_iff (mul_ne_zero hq.ne' hne)]
  have ht : δ * (1 - (C ()).w .a) / xorNuL δ ((C ()).w .a) * xorNuL δ ((C ()).w .a) =
      δ * (1 - (C ()).w .a) := div_mul_cancel₀ _ hne
  unfold xorNuL at ht ⊢
  linear_combination (X * (C ()).w .a) * ht

/-- **`e(refuse) = −X·δ(1−q)/ν_L`** at `0 < 1 − q`, `ν_L > 0`.
Source: dp-sl-054; mandate T13(a). Kind: P. Fidelity: exact. Hyps: (a) `0 < 1 − q`, `0 < ν_L` -/
theorem xorE_refuse (hq : 0 < (C ()).w .b) (hL : 0 < xorNuL δ ((C ()).w .a)) :
    xorE δ h0 h1 c X C .b = -(X * (δ * (1 - (C ()).w .a) / xorNuL δ ((C ()).w .a))) := by
  unfold xorE condExp
  rw [xor_paySum_act_L, xor_nu_act_L]
  simp only [reduceCtorEq, if_false]
  have hne : xorNuL δ ((C ()).w .a) ≠ 0 := hL.ne'
  rw [div_eq_iff (mul_ne_zero hq.ne' hne)]
  have ht : δ * (1 - (C ()).w .a) / xorNuL δ ((C ()).w .a) * xorNuL δ ((C ()).w .a) =
      δ * (1 - (C ()).w .a) := div_mul_cancel₀ _ hne
  unfold xorNuL at ht ⊢
  linear_combination (X * (C ()).w .b) * ht

/-- **Conditioning refuses by exactly `c`**: `e(pay) = e(refuse) − c` at a properly mixed label.
Source: dp-sl-054 ("EV = R2-real = R3 refuse by `c`"); P06-1′; mandate T13(a)
Kind: P
Fidelity: exact
Hyps: (a) `0 < q < 1`, `0 < ν_L` -/
theorem xorE_sub (hqa : 0 < (C ()).w .a) (hqb : 0 < (C ()).w .b) (hL : 0 < xorNuL δ ((C ()).w .a)) :
    xorE δ h0 h1 c X C .a = xorE δ h0 h1 c X C .b - c := by
  rw [xorE_pay δ h0 h1 c X C hqa hL, xorE_refuse δ h0 h1 c X C hqb hL]; ring

/-- **The disaster conditional is the same for both acts**: `P(D = 1 ∣ L, a) = δ(1−q)/ν_L`.
Source: dp-sl-054 ("the disaster conditional is the same for both acts"); P06-1′ ("paying is no
evidence against termites"); mandate T13(a)
Kind: P
Fidelity: exact
Hyps: (a) `0 < C(d_L)(a)`, `0 < ν_L` -/
theorem xor_disaster_same (a : Act2) (ha : 0 < (C ()).w a) (hL : 0 < xorNuL δ ((C ()).w .a)) :
    nu C (xorTree δ h0 h1 c X) (xorD ∩ xorActEv () a ∩ xorObs ()) /
      nu C (xorTree δ h0 h1 c X) (xorActEv () a ∩ xorObs ()) =
      δ * (1 - (C ()).w .a) / xorNuL δ ((C ()).w .a) := by
  rw [xor_nu_D_act_L, xor_nu_act_L]
  field_simp
  try ring

/-- `ν(lie ∧ L) = q(1−q)` and `ν(lie ∧ pay ∧ L) = δ(1−q)q`. Source: none: infrastructure. Kind: L -/
theorem xor_nu_lie :
    nu C (xorTree δ h0 h1 c X) (xorLie ∩ xorObs ()) = (C ()).w .a * (1 - (C ()).w .a) ∧
      nu C (xorTree δ h0 h1 c X) (xorLie ∩ xorActEv () .a ∩ xorObs ()) =
        δ * (1 - (C ()).w .a) * (C ()).w .a := by
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  constructor <;>
  · rw [nu_eq_sum, xorTree_sum]
    simp [Act2.sum_univ, xorTree, xorWorld, xorPayW, xorLetter, xorTermites, Fin.sum_univ_two, xorObs, xorActEv, xorLie,
      FinDistr.coin]
    rw [hb]; ring

/-- **The letter is false on letter runs w.p. `q(1−q)/ν_L`** (the live draw differs from the
simulation's). Source: P06-1′ ("`P(false ∣ L=1) = q(1−q)/(δ(1−q)+(1−δ)q)`"); mandate T13(a).
Kind: P. Fidelity: exact. Hyps: (a) `0 < ν_L` -/
theorem xor_lie_given_L (hL : 0 < xorNuL δ ((C ()).w .a)) :
    nu C (xorTree δ h0 h1 c X) (xorLie ∩ xorObs ()) / nu C (xorTree δ h0 h1 c X) (xorObs ()) =
      (C ()).w .a * (1 - (C ()).w .a) / xorNuL δ ((C ()).w .a) := by
  rw [(xor_nu_lie δ h0 h1 c X C).1, xor_nu_L]

/-- **On pay runs the letter is false w.p. `δ(1−q)/ν_L`** — identically the disaster conditional:
"paying is no evidence against termites" is "the honest predictor's letter lied on the very runs
conditioned on". (The mandate's "`p(q) = q(1−q)/…` on pay-runs" conflates the two; P06.md's
`p(q)` is `δ(1−q)/ν_L`, and `q(1−q)/ν_L` is the unconditional rate — findings F-P.)
Source: P06-1′ ("`P(false ∣ L=1, pay) = p(q) = P(D=1 ∣ L=1, pay)` identically"); mandate T13(a)
Kind: P
Fidelity: exact
Hyps: (a) `0 < q`, `0 < ν_L` -/
theorem xor_lie_given_pay (hq : 0 < (C ()).w .a) (hL : 0 < xorNuL δ ((C ()).w .a)) :
    nu C (xorTree δ h0 h1 c X) (xorLie ∩ xorActEv () .a ∩ xorObs ()) /
      nu C (xorTree δ h0 h1 c X) (xorActEv () .a ∩ xorObs ()) =
      δ * (1 - (C ()).w .a) / xorNuL δ ((C ()).w .a) := by
  rw [(xor_nu_lie δ h0 h1 c X C).2, xor_nu_act_L]
  field_simp
  try ring

/-! ### The deviation referent and the policy values -/

/-- The deviation referent R1-state at the letter point: `𝔼_{μ_{C[d_L ↦ a]}}[r ∣ L = 1]`.
Source: P06.md vocabulary ("R1-state = the `O_L`-conditioned all-instance deviation"). Kind: D -/
noncomputable def xorR1State (a : Act2) : ℚ :=
  condExp (C.deviatePure () a) (xorTree δ h0 h1 c X) (xorObs ())

/-- **R1-state pays**: `R1(pay) = −c` (the all-instance deviation to pay makes every letter a
no-termites letter) and `R1(refuse) = −X`; the margin is `X − c`.
Source: dp-sl-054 ("R1-state pays under both semantics"); mandate T13(a) ("state the margin")
Kind: P
Fidelity: exact
Hyps: (a) `0 < δ < 1` (both letters realizable) -/
theorem xorR1State_pay (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    xorR1State δ h0 h1 c X C .a = -c ∧ xorR1State δ h0 h1 c X C .b = -X := by
  unfold xorR1State condExp
  have hδ : δ ≠ 0 := hδ0.ne'
  have h1δ : (1 - δ) ≠ 0 := (sub_pos.mpr hδ1).ne'
  constructor <;>
  · rw [paySum_eq_sum_ite, nu_eq_sum, xorTree_sum, xorTree_sum, Proc.deviatePure, deviate_unit]
    simp [Act2.sum_univ, xorTree, xorWorld, xorPayW, xorLetter, xorTermites, Fin.sum_univ_two, xorObs,
      FinDistr.coin, FinDistr.pure]
    field_simp
    try ring

/-- **The policy values under Definition 6**: `V(pay) = −Xδ − c(1−δ)`, `V(refuse) = −Xδ`.
Source: P06.md line 7 ("Policy values under both semantics: `V(pay) = −Xδ − c(1−δ) = −10990`,
`V(refuse) = −Xδ = −10000`"); mandate T13(c)
Kind: L (the plan pre-labels it)
Fidelity: exact -/
theorem xor_policy_values :
    value (Proc.ofFun fun _ => Act2.a) (xorTree δ h0 h1 c X) = -X * δ - c * (1 - δ) ∧
      value (Proc.ofFun fun _ => Act2.b) (xorTree δ h0 h1 c X) = -X * δ := by
  unfold value
  constructor <;>
  · rw [xorTree_sum]
    simp [Act2.sum_univ, xorTree, xorWorld, xorPayW, xorLetter, xorTermites, Fin.sum_univ_two, FinDistr.coin,
      Proc.ofFun]
    ring

/-- The Levinstein–Soares numbers: `−10990` vs `−10000` at `δ = 1/100`, `c = 1000`, `X = 10⁶`.
Source: P06.md line 7; dp-sl-2-068. Kind: N+ -/
theorem xor_policy_values_LS :
    value (Proc.ofFun fun _ => Act2.a) (xorTree (1/100) (by norm_num) (by norm_num) 1000 1000000) = -10990 ∧
      value (Proc.ofFun fun _ => Act2.b) (xorTree (1/100) (by norm_num) (by norm_num) 1000 1000000) = -10000 := by
  obtain ⟨h1, h2⟩ := xor_policy_values (1/100) (by norm_num) (by norm_num) 1000 1000000
  rw [h1, h2]; norm_num

/-! ### F3′ at the real node and the tremble-pinned values -/

/-- XOR's action events are disjoint. Source: none: infrastructure. Kind: L -/
theorem xor_disjointActEv : DisjointActEv xorActEv () := by
  intro a b hab
  rw [Finset.disjoint_left]
  intro w hw hw'
  simp only [xorActEv, Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
  exact hab (Option.some_injective _ (hw.symm.trans hw'))

/-- **F3′ holds structurally on XOR at the letter point**: on every letter leaf the real node
(below the sample) is node-action-veridical and subtree-veridical for `L = 1`, and the
simulation node is not node-action-veridical (its edge is the sample, the world records the live
act or `none`).
Source: P06.md line 7 ("F3′ holds at the real node under Def 6"); mandate T13(a), T7(e) (a second
N+ with `O_d ≠ ⊤`)
Kind: P
Fidelity: exact -/
theorem xor_actRecordingStruct : ActRecordingStruct xorObs xorActEv (xorTree δ h0 h1 c X) () := by
  refine ⟨?_, ?_⟩
  · -- node-action-veridical `d`-nodes are subtree-veridical for `L = 1`
    rintro ⟨i, q⟩ - hnav
    rcases q with _ | ⟨x, q'⟩
    · -- the simulation node is not node-action-veridical: the leaf `(x = pay, a = refuse)`
      exfalso
      have := hnav ⟨i, .a, .b, ()⟩ .a (by simp [xorTree, edgeOf])
      simp [xorTree, xorWorld, xorActEv] at this
    · rcases q' with _ | ⟨a, q''⟩
      · -- a live node: node-action-veridical only on a letter branch, where every leaf has `L = 1`
        rintro ⟨j, x', a', ⟨⟩⟩ hℓ
        rw [mem_leavesBelow] at hℓ
        by_cases hj : j = i
        · subst hj
          by_cases hx : x' = x
          · subst hx
            have := hnav ⟨j, x', a', ()⟩ a' (by simp [xorTree, edgeOf])
            simp [xorTree, xorWorld, xorActEv] at this
            by_cases hL : xorLetter (xorTermites j) x' = true
            · simp [xorTree, xorWorld, xorObs, hL]
            · simp [hL] at this
          · simp [xorTree, edgeOf, hx] at hℓ
        · simp [xorTree, edgeOf, hj] at hℓ
      · exact q''.elim
  · -- every chance-positive letter leaf passes exactly one node-action-veridical `d`-node
    rintro ⟨i, x, a, ⟨⟩⟩ - hO
    have hL : xorLetter (xorTermites i) x = true := by
      simpa [xorTree, xorWorld, xorObs] using hO
    refine ⟨⟨i, some ⟨x, none⟩⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_dNodesOn]; exact ⟨rfl, by simp [xorTree, edgeOf]⟩
    · rintro ⟨j, x', a', ⟨⟩⟩ a'' he
      by_cases hj : j = i
      · subst hj
        by_cases hx : x' = x
        · subst hx
          simp [xorTree, edgeOf] at he
          subst he
          simp [xorTree, xorWorld, xorActEv, hL]
        · simp [xorTree, edgeOf, hx] at he
      · simp [xorTree, edgeOf, hj] at he
    · rintro ⟨j, q'⟩ ⟨hq, hnav⟩
      rw [mem_dNodesOn] at hq
      obtain ⟨-, hsome⟩ := hq
      rcases q' with _ | ⟨x', q''⟩
      · exfalso
        have := hnav ⟨j, .a, .b, ()⟩ .a (by simp [xorTree, edgeOf])
        simp [xorTree, xorWorld, xorActEv] at this
      · rcases q'' with _ | ⟨a', q'''⟩
        · by_cases hj : i = j
          · subst hj
            by_cases hx : x = x'
            · subst hx; rfl
            · simp [xorTree, edgeOf, hx] at hsome
          · simp [xorTree, edgeOf, hj] at hsome
        · exact q'''.elim

/-- The standing hypothesis at the letter point: `ν_{C[d ↦ m]}(L = 1) = ν_L(m(pay)) > 0` for
`0 < δ < 1`. Source: C2-7; mandate T7(e) ("`R m = δ(1 − m(pay)) + (1−δ)m(pay) > 0`"). Kind: L -/
theorem xor_hStand (hδ0 : 0 < δ) (hδ1 : δ < 1) (m : FinDistr ℚ Act2) :
    0 < nu (C.deviate () m) (xorTree δ h0 h1 c X) (xorObs ()) := by
  rw [xor_nu_L, deviate_unit]
  have hs := m.sum_one
  rw [Act2.sum_univ] at hs
  have ha := m.nonneg .a
  have hb := m.nonneg .b
  simp only [xorNuL]
  have h1q : 0 ≤ 1 - m.w .a := by linarith
  have t1 : 0 ≤ δ * (1 - m.w .a) := mul_nonneg hδ0.le h1q
  rcases ha.lt_or_eq with hq | hq
  · have : 0 < (1 - δ) * m.w .a := mul_pos (by linarith) hq
    linarith
  · rw [← hq]; simp; exact hδ0

/-- `Q_pay(m)` and `Q_refuse(m)` on XOR (the one-draw-erased leaf sums).
Source: none: infrastructure. Kind: L -/
theorem xor_qSum (m : FinDistr ℚ Act2) :
    qSum (C.deviate () m) () .a (xorTree δ h0 h1 c X) (xorActEv () .a ∩ xorObs ()) =
        δ * m.w .b * (-c - X) + (1 - δ) * m.w .a * (-c) ∧
      qSum (C.deviate () m) () .b (xorTree δ h0 h1 c X) (xorActEv () .b ∩ xorObs ()) =
        δ * m.w .b * (-X) := by
  constructor <;>
  · unfold qSum reducedWeight worldEv
    rw [Finset.sum_filter, xorTree_sum, deviate_unit]
    simp [Act2.sum_univ, xorTree, xorWorld, xorPayW, xorLetter, xorTermites, Fin.sum_univ_two, xorActEv, xorObs,
      FinDistr.coin, List.erase_cons]
    try ring

/-- **R3 = conditioning at every label, boundary included**: the tremble-pinned values at the
letter point are `(−c − X·δ(1−m)/ν_L(m), −X·δ(1−m)/ν_L(m))`, `m := m(pay)`.
Source: dp-sl-054 ("EV = R2-real = R3 refuse by `c`"); mandate T13(a)
Kind: P
Fidelity: exact
Hyps: (a) `0 < δ < 1` -/
theorem xorR3 (hδ0 : 0 < δ) (hδ1 : δ < 1) (m : FinDistr ℚ Act2) :
    r3Val xorObs xorActEv C (xorTree δ h0 h1 c X) () m .a =
        -c - X * (δ * (1 - m.w .a) / xorNuL δ (m.w .a)) ∧
      r3Val xorObs xorActEv C (xorTree δ h0 h1 c X) () m .b =
        -(X * (δ * (1 - m.w .a) / xorNuL δ (m.w .a))) := by
  have hs := m.sum_one
  rw [Act2.sum_univ] at hs
  have hb : m.w .b = 1 - m.w .a := by linarith
  have hL : 0 < xorNuL δ (m.w .a) := by
    have := xor_hStand δ h0 h1 c X C hδ0 hδ1 m
    rwa [xor_nu_L, deviate_unit] at this
  constructor
  · rw [r3Val_eq_qSum_div xorObs xorActEv (xor_actRecordingStruct δ h0 h1 c X) xor_disjointActEv C m
      .a (xor_hStand δ h0 h1 c X C hδ0 hδ1 m), (xor_qSum δ h0 h1 c X C m).1, xor_nu_L]
    simp only [deviate_unit]
    rw [hb]
    have hne : xorNuL δ (m.w .a) ≠ 0 := hL.ne'
    rw [div_eq_iff hne]
    have ht : δ * (1 - m.w .a) / xorNuL δ (m.w .a) * xorNuL δ (m.w .a) = δ * (1 - m.w .a) :=
      div_mul_cancel₀ _ hne
    unfold xorNuL at ht ⊢
    linear_combination X * ht
  · rw [r3Val_eq_qSum_div xorObs xorActEv (xor_actRecordingStruct δ h0 h1 c X) xor_disjointActEv C m
      .b (xor_hStand δ h0 h1 c X C hδ0 hδ1 m), (xor_qSum δ h0 h1 c X C m).2, xor_nu_L]
    simp only [deviate_unit]
    rw [hb]
    have hne : xorNuL δ (m.w .a) ≠ 0 := hL.ne'
    rw [div_eq_iff hne]
    have ht : δ * (1 - m.w .a) / xorNuL δ (m.w .a) * xorNuL δ (m.w .a) = δ * (1 - m.w .a) :=
      div_mul_cancel₀ _ hne
    unfold xorNuL at ht ⊢
    linear_combination X * ht

/-! ### The shared seed -/

/-- The 6′ run law on XOR: `μ'(i, x, a) = coin(i)·C(d_L)(x)·[x = a]` — the live draw is the sample.
Source: `seeds.md` Definition 6′; P06.md line 7 ("Def 6′: `a = x`"). Kind: P. Fidelity: exact -/
theorem xor_leafLaw' (i : Fin 2) (x a : Act2) :
    leafLaw' C (xorTree δ h0 h1 c X) ⟨i, ⟨x, ⟨a, ()⟩⟩⟩ =
      (FinDistr.coin δ h0 h1).w i * (C ()).w x * (if x = a then 1 else 0) := by
  unfold leafLaw' xorTree
  rw [leafLawSeed_chance, leafLawSeed_decision_of_none C rfl,
    leafLawSeed_decision_of_some C (a' := x) (by simp)]
  simp only [leafLawSeed_leaf]
  split_ifs <;> ring

/-- `ν'(pay ∧ L) = (1−δ)q`, `ν'(refuse ∧ L) = δ(1−q)`. Source: none: infrastructure. Kind: L -/
theorem xor_nu'_act_L :
    nu' C (xorTree δ h0 h1 c X) (xorActEv () .a ∩ xorObs ()) = (1 - δ) * (C ()).w .a ∧
      nu' C (xorTree δ h0 h1 c X) (xorActEv () .b ∩ xorObs ()) = δ * (1 - (C ()).w .a) := by
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  constructor <;>
  · rw [nu'_eq_sum_ite, xorTree_sum]
    simp only [xor_leafLaw']
    simp [Act2.sum_univ, Fin.sum_univ_two, xorTree, xorWorld, xorLetter, xorTermites, xorObs,
      xorActEv, FinDistr.coin]
    try (rw [hb]; ring)
    try simp

/-- `𝔼'[r · 1_{pay ∧ L}] = (1−δ)q·(−c)`, `𝔼'[r · 1_{refuse ∧ L}] = δ(1−q)·(−X)`.
Source: none: infrastructure. Kind: L -/
theorem xor_paySumSeed_act_L :
    paySumSeed C (xorTree δ h0 h1 c X) (xorActEv () .a ∩ xorObs ()) = (1 - δ) * (C ()).w .a * (-c) ∧
      paySumSeed C (xorTree δ h0 h1 c X) (xorActEv () .b ∩ xorObs ()) =
        δ * (1 - (C ()).w .a) * (-X) := by
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  constructor <;>
  · rw [paySumSeed_eq_sum_ite, xorTree_sum]
    simp only [xor_leafLaw']
    simp [Act2.sum_univ, Fin.sum_univ_two, xorTree, xorWorld, xorPayW, xorLetter, xorTermites,
      xorObs, xorActEv, FinDistr.coin]
    try (rw [hb]; ring)
    try simp

/-- The 6′ conditional act value at the letter point. Source: P06-1′. Kind: D. Fidelity: variant: 6′ -/
noncomputable def xorE' (a : Act2) : ℚ :=
  condExpSeed C (xorTree δ h0 h1 c X) (xorActEv () a ∩ xorObs ())

/-- **Under 6′ `e'(pay) = −c` and `e'(refuse) = −X`**: evidential choice pays by `X − c` at every
properly mixed label with `0 < δ < 1`.
Source: P06-1′ ("evidential choice pays (`X − c`) at every strict, masked and limit state");
dp-sl-2-016; mandate T13(b)
Kind: P
Fidelity: variant: 6′
Hyps: (a) `0 < q < 1`, `0 < δ < 1` -/
theorem xorE'_values (hδ0 : 0 < δ) (hδ1 : δ < 1) (hqa : 0 < (C ()).w .a) (hqb : 0 < (C ()).w .b) :
    xorE' δ h0 h1 c X C .a = -c ∧ xorE' δ h0 h1 c X C .b = -X ∧
      xorE' δ h0 h1 c X C .a - xorE' δ h0 h1 c X C .b = X - c := by
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have h1q : 0 < 1 - (C ()).w .a := by linarith
  have h1δ : (1 - δ) ≠ 0 := (sub_pos.mpr hδ1).ne'
  have hδ : δ ≠ 0 := hδ0.ne'
  have ha : xorE' δ h0 h1 c X C .a = -c := by
    unfold xorE' condExpSeed
    rw [(xor_paySumSeed_act_L δ h0 h1 c X C).1, (xor_nu'_act_L δ h0 h1 c X C).1]
    field_simp
  have hb' : xorE' δ h0 h1 c X C .b = -X := by
    unfold xorE' condExpSeed
    rw [(xor_paySumSeed_act_L δ h0 h1 c X C).2, (xor_nu'_act_L δ h0 h1 c X C).2]
    field_simp
  exact ⟨ha, hb', by rw [ha, hb']; ring⟩

/-- **The shared-seed value is affine in `q`**: `V'(q) = −δX − (1−δ)cq` — no mixed label is forced
(P05's Case-2 apparatus is idle under 6′).
Source: dp-sl-2-016 ("the shared-seed evidential value is affine in `q`"); mandate T13(b)
Kind: P
Fidelity: variant: 6′ -/
theorem xor_value' : value' C (xorTree δ h0 h1 c X) = -δ * X - (1 - δ) * c * (C ()).w .a := by
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  unfold value'
  rw [xorTree_sum]
  simp only [xor_leafLaw']
  simp [Act2.sum_univ, Fin.sum_univ_two, xorTree, xorPayW, xorLetter, xorTermites, FinDistr.coin]
  rw [hb]; ring

/-- **The policy values under 6′ agree with Definition 6's**: `V'(pay) = −Xδ − c(1−δ)`,
`V'(refuse) = −Xδ` (deterministic procedures have one run law); the deviation evaluator under 6′
therefore refuses by `(1−δ)c`.
Source: P06.md line 7 ("Policy values under both semantics"); dp-sl-2-016 ("the deviation-based
evaluator `{refuse}`"); mandate T13(b)(c)
Kind: L
Fidelity: variant: 6′ -/
theorem xor_policy_values' :
    value' (Proc.ofFun fun _ => Act2.a) (xorTree δ h0 h1 c X) = -X * δ - c * (1 - δ) ∧
      value' (Proc.ofFun fun _ => Act2.b) (xorTree δ h0 h1 c X) = -X * δ := by
  constructor <;> (rw [xor_value']; simp [Proc.ofFun]; ring)

/-- **The do-CDT construal under 6′** (SE-1(d)): the seed routes the letter (letter runs have
mass `δ(1−q)` with `D = 1` and `(1−δ)q` with `D = 0`), the real node is forced to `a`, conditioned
on `L = 1` — definable from the tree, not a 6′ run-law quantity (disclosed construal).
Source: `seeds.md` SE-1(d); P06.md vocabulary ("do-CDT = the same forcing under Def 6′ with the
seed still routing the letter, conditioned on `L=1`"); mandate T13(b)
Kind: D
Fidelity: variant: SE-1(d)'s definable-not-intrinsic construal -/
noncomputable def xorDoCdt' (a : Act2) : ℚ :=
  (δ * (1 - (C ()).w .a) * xorPayW c X true .b a + (1 - δ) * (C ()).w .a * xorPayW c X false .a a) /
    xorNuL δ ((C ()).w .a)

/-- **do-CDT refuses by exactly `c`** under 6′ (at `ν_L > 0`).
Source: dp-sl-2-016 ("do-CDT (SE-1(d)'s definable forcing) `{refuse}`"); mandate T13(b)
Kind: P
Fidelity: variant: do-construal
Hyps: (a) `0 < ν_L` -/
theorem xorDoCdt'_sub (hL : 0 < xorNuL δ ((C ()).w .a)) :
    xorDoCdt' δ c X C .a - xorDoCdt' δ c X C .b = -c := by
  unfold xorDoCdt'
  have hne : xorNuL δ ((C ()).w .a) ≠ 0 := hL.ne'
  rw [← sub_div, div_eq_iff hne]
  simp [xorPayW, xorLetter]
  unfold xorNuL; ring

/-- **The forecast table** (Definition 6): a deterministic refuser receiving the letter forecasts
disaster with certainty, `P(D = 1 ∣ L, refuse) = 1`; at the label `q = ½` both acts forecast `δ`.
Source: dp-sl-2-016 (P08-11′'s forecast table: "`= 1` at `m = 0` under Definition 6 … at the
masked grade (`m = ½`) both agents forecast `δ`"); mandate T13(b)
Kind: P / N+
Fidelity: exact (Definition 6 conditionals at the two labels)
Hyps: (a) `0 < δ < 1` -/
theorem xor_forecast (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    nu (Proc.ofFun fun _ => Act2.b) (xorTree δ h0 h1 c X) (xorD ∩ xorActEv () .b ∩ xorObs ()) /
      nu (Proc.ofFun fun _ => Act2.b) (xorTree δ h0 h1 c X) (xorActEv () .b ∩ xorObs ()) = 1 ∧
    ∀ a : Act2,
      nu (procQ (1/2) (by norm_num) (by norm_num)) (xorTree δ h0 h1 c X)
          (xorD ∩ xorActEv () a ∩ xorObs ()) /
        nu (procQ (1/2) (by norm_num) (by norm_num)) (xorTree δ h0 h1 c X)
          (xorActEv () a ∩ xorObs ()) = δ := by
  have hδ : δ ≠ 0 := hδ0.ne'
  have hN : xorNuL δ (1/2) = 1/2 := by unfold xorNuL; ring
  constructor
  · rw [xor_nu_D_act_L, xor_nu_act_L]
    simp [Proc.ofFun, xorNuL, hδ]
  · intro a
    rw [xor_nu_D_act_L, xor_nu_act_L]
    cases a <;> simp only [procQ, FinDistr.act2_a, FinDistr.act2_b] <;> rw [hN] <;> ring

/-! ### Implementability (T13(d)) -/

end tree

/-- A *structurally pre-query* event for `d`: decided at every `d`-node met on an `O_d`-run (no
positivity: the shared-seed law has no `leafLaw` guard).
Source: P06.md vocabulary ("pre-query event"); `dp-core-tree`'s `PreQuery` (positivity-guarded)
Kind: D -/
def PreQueryStruct {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
    [∀ d, DecidableEq (acts d)] [DecidableEq ι] (obs : ι → Finset Ω) (B : Tree Ω ι acts ℚ) (d : ι)
    (X : Finset Ω) : Prop :=
  ∀ ℓ, world B ℓ ∈ obs d → ∀ q, pt B q = d → (edgeOf B q ℓ).isSome → DecidedAt B q X

/-- **Mixed-strategy implementability at `d` under 6′** (P05's "the act's only parent is the
decision", transcribed tree-side): the live act is independent of every structurally pre-query
event on `O_d`-runs under the shared-seed law:
`ν'(a ∧ X ∧ O_d)·ν'(O_d) = ν'(X ∧ O_d)·ν'(a ∧ O_d)` whenever `ν'(X ∧ O_d) > 0`.
Source: P06.md vocabulary ("the real draw is independent of every pre-query event given the
label"); P06-11′; dp-sl-2-018; mandate T13(d)
Kind: D
Fidelity: exact (cross-multiplied) -/
def ImplementableSeed {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
    [∀ d, DecidableEq (acts d)] [DecidableEq ι] (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
    (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (d : ι) : Prop :=
  ∀ X, PreQueryStruct obs B d X → 0 < nu' C B (X ∩ obs d) → ∀ a,
    nu' C B (actEv d a ∩ X ∩ obs d) * nu' C B (obs d) = nu' C B (X ∩ obs d) * nu' C B (actEv d a ∩ obs d)

/-- The same identities under Definition 6. Source: P06-11′ ("under Definition 6 it holds at every
fiber"); mandate T13(d). Kind: D -/
def ImplementableDef6 {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
    [∀ d, DecidableEq (acts d)] [DecidableEq ι] (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
    (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (d : ι) : Prop :=
  ∀ X, PreQueryStruct obs B d X → 0 < nu C B (X ∩ obs d) → ∀ a,
    nu C B (actEv d a ∩ X ∩ obs d) * nu C B (obs d) = nu C B (X ∩ obs d) * nu C B (actEv d a ∩ obs d)

section impl

variable (δ : ℚ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (c X : ℚ) (C : Proc Unit (fun _ => Act2) ℚ)

/-- Termites is structurally pre-query on XOR: every `d_L`-node lies below the chance root, so the
leaves below it share `D`. Source: P06.md line 7; mandate T13(d). Kind: L -/
theorem xor_preQuery_D : PreQueryStruct xorObs (xorTree δ h0 h1 c X) () xorD := by
  rintro ⟨i, x, a, ⟨⟩⟩ _ ⟨j, q'⟩ _ hsome
  have hij : i = j := by
    by_contra h
    simp [xorTree, edgeOf, h] at hsome
  subst hij
  unfold DecidedAt
  by_cases hD : xorTermites i = true
  · left
    rintro ⟨j', x', a', ⟨⟩⟩ hℓ
    rw [mem_leavesBelow] at hℓ
    by_cases hj : j' = i
    · subst hj; simp [xorTree, xorWorld, xorD, hD]
    · simp [xorTree, edgeOf, hj] at hℓ
  · right
    rintro ⟨j', x', a', ⟨⟩⟩ hℓ
    rw [mem_leavesBelow] at hℓ
    by_cases hj : j' = i
    · subst hj; simp [xorTree, xorWorld, xorD, hD]
    · simp [xorTree, edgeOf, hj] at hℓ

/-- `ν'(pay ∧ D ∧ L) = 0`, `ν'(D ∧ L) = δ(1−q)` under 6′ (a letter with termites is a refuse letter).
Source: P06-11′ ("6′: `0` given `D=1`"). Kind: L -/
theorem xor_nu'_D :
    nu' C (xorTree δ h0 h1 c X) (xorActEv () .a ∩ xorD ∩ xorObs ()) = 0 ∧
      nu' C (xorTree δ h0 h1 c X) (xorD ∩ xorObs ()) = δ * (1 - (C ()).w .a) ∧
      nu' C (xorTree δ h0 h1 c X) (xorObs ()) = δ * (1 - (C ()).w .a) + (1 - δ) * (C ()).w .a := by
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [nu'_eq_sum_ite, xorTree_sum]
    simp only [xor_leafLaw']
    simp [Act2.sum_univ, Fin.sum_univ_two, xorTree, xorWorld, xorLetter, xorTermites, xorObs,
      xorActEv, xorD, FinDistr.coin]
    try (rw [hb]; ring)
    try simp

/-- **T13(d): XOR is not implementable at `d_L` under 6′** — against the pre-query event `D = 1`:
`ν'(pay ∣ D = 1, L) = 0` while `ν'(pay ∣ L) = (1−δ)q/ν_L > 0`.
Source: P06-1′ ("mixed-strategy implementability fails — `ν'(pay ∣ D=1, reached) = 0` and
`ν'(pay ∣ D=0, reached) = 1` against `q`"); dp-sl-2-018 (the XOR witness); mandate T13(d)
Kind: P
Fidelity: exact
Hyps: (a) `0 < δ < 1`, `0 < q < 1` -/
theorem xor_not_implementableSeed (hδ0 : 0 < δ) (hδ1 : δ < 1) (hqa : 0 < (C ()).w .a)
    (hqb : 0 < (C ()).w .b) : ¬ ImplementableSeed xorObs xorActEv C (xorTree δ h0 h1 c X) () := by
  intro h
  obtain ⟨h1', h2', h3'⟩ := xor_nu'_D δ h0 h1 c X C
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hpos : 0 < nu' C (xorTree δ h0 h1 c X) (xorD ∩ xorObs ()) := by
    rw [h2']; exact mul_pos hδ0 (by linarith)
  have := h xorD (xor_preQuery_D δ h0 h1 c X) hpos .a
  rw [h1', h2', (xor_nu'_act_L δ h0 h1 c X C).1] at this
  have : 0 < δ * (1 - (C ()).w .a) * ((1 - δ) * (C ()).w .a) :=
    mul_pos (mul_pos hδ0 (by linarith)) (mul_pos (by linarith) hqa)
  linarith

/-- **Under Definition 6 the same identities hold on XOR** for the pre-query events `D = 1` and
`D = 0` and both acts (the live draw is independent of everything so far).
Source: P06-11′ ("under Definition 6 it holds at every fiber by Definition 6's independence
clause"); mandate T13(d)
Kind: P
Fidelity: exact (the two pre-query events of the source's witness) -/
theorem xor_implementable_def6_D (a : Act2) :
    nu C (xorTree δ h0 h1 c X) (xorActEv () a ∩ xorD ∩ xorObs ()) * nu C (xorTree δ h0 h1 c X) (xorObs ()) =
        nu C (xorTree δ h0 h1 c X) (xorD ∩ xorObs ()) * nu C (xorTree δ h0 h1 c X) (xorActEv () a ∩ xorObs ()) ∧
      nu C (xorTree δ h0 h1 c X) (xorActEv () a ∩ xorNotD ∩ xorObs ()) * nu C (xorTree δ h0 h1 c X) (xorObs ()) =
        nu C (xorTree δ h0 h1 c X) (xorNotD ∩ xorObs ()) * nu C (xorTree δ h0 h1 c X) (xorActEv () a ∩ xorObs ()) := by
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  constructor <;>
  · simp only [nu_eq_sum, xorTree_sum]
    cases a <;>
      simp [Act2.sum_univ, Fin.sum_univ_two, xorTree, xorWorld, xorLetter, xorTermites, xorObs,
        xorActEv, xorD, xorNotD, FinDistr.coin] <;>
      rw [hb] <;> ring

end impl

/-- **OPEN (the ⇐ direction of P06-11′ in its almost-fair case)**: at an F3′-structural point of
an almost-fair tree (no run meets two `d`-nodes — the "no path-relevant nesting" clause holds
vacuously), the point is implementable under 6′. Route: on almost-fair trees the shared-seed law
equals the Definition-6 law (`dp-core-tree`'s `AlmostFair.leafLaw_eq_leafLaw'`), so the claim is
the Definition-6 identity for a pre-query event, which needs the F3′ recording lemma relativized
to `X ∩ O_d` with the nodes where `X` is decided negatively handled separately — not done. The
general clause ("every earlier `d`-instance on the path routes to identical subtrees") is not
defined here; this special case is the precise statement a continuation can close.
Source: P06-11′ ("the ⇐ direction … argued, not machine-checked"); dp-sl-2-018; mandate T13(d)
(`implementable_of_pathIrrelevant_open`, stated here for the almost-fair case)
Kind: OPEN
Fidelity: weaker: almost-fair in place of path-irrelevant nesting -/
theorem implementable_of_almostFair_open {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type}
    [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] [DecidableEq ι] (obs : ι → Finset Ω)
    (actEv : (d : ι) → acts d → Finset Ω) (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (d : ι)
    (_hF : ActRecordingStruct obs actEv B d) (_hdisj : DisjointActEv actEv d) (_hAF : AlmostFair B) :
    ImplementableSeed obs actEv C B d := by
  sorry

end Cleanroom.Decision.DpDutchBook
