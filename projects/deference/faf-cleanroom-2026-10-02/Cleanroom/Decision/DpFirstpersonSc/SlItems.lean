import Cleanroom.Decision.DpCalibration.Theories
import Cleanroom.Decision.DpCalibration.Recording
import Cleanroom.Decision.DpCalibration.MiniDevices
import Cleanroom.Decision.DpFaithfulUdt.Procs

/-!
# The Smoking-Lesion-sequence items: CEDT at self-transparent points, matching pennies and the
`2×2` tie — T17(a)(b) of [[dp-firstperson-sc-mandate]]

* **T17(a), P02-8′'s CEDT rule of record** (`CEDT`): strict observation calibration ∧
  `T_CDT`-approval (Definition 18 at the state's counterfactual slot `cf`), *at self-transparent
  points* (`CEDTSelfTransparent` adds Appendix B item 2's `P_{s_d}(a) = C(d)(a)`). At
  Definition-7-recorded points with `ν(O_d) > 0`, strict OC already gives self-transparency
  (`dp-calibration`'s `selfTransparent_of_recordsFor_strict`, cited: `cedt_selfTransparent_of_recordsFor`),
  so there CEDT is `T_CDT`-approval at the calibrated state. **Miniature instance**
  (`miniature_cedt_iff`): with the forcing referent `cf` (R2-real: the live node forced to the act,
  the predictor's sample still `q`, realized as the tree `miniForced a`), the strictly-calibrated-
  and-CEDT-approved labels on Remark 4.3's miniature are exactly `{2/3}` — unlike `T_EDT`, which
  approves the pure labels vacuously (`miniature_tEdt_pure_a/b`), `T_CDT` is total and rejects
  them (`V^a = 2(1−q)` vs `V^b = q`).
* **T17(b), P03-6 / dp-sl-2-048, matching pennies against a predictor of skill `p`**
  (`pennies p u`): the agent draws `a ∼ C(d)`; Omega's guess equals the draw with probability `p`,
  else an independent sample `b ∼ C(d)` (a second `d`-node). **Shape disclosure (fidelity:
  variant):** the sample `b` is drawn *before* the draw-keyed chance node on every path, so the
  leaf type is uniform (`Σ a, Σ b, Σ i, Unit`) and `#_d = 2` on every path (the source draws the
  sample only on the independent branch, `#_d = 2` there and `1` on the copy branch); the law of
  `(act, guess)` is identical, and the strict-OC state at `O = ⊤`, the act events `{act = a}` and
  the tremble polynomials read only that law. **Theorem** (`pennies_adviceEdt_iff`): the label
  `q` is `T_EDT`-approved in the tremble limit (`dp-calibration`'s D4 `AdviceEdt`, the advice-stance
  evaluator whose act values are tremble limits, `limitVal`) iff `supp q ⊆ argmax_a EV(a)` with
  `EV(a) = p·u(a,a) + (1−p)·∑_b q_b·u(a,b)` — the symmetric game's best-reply condition against
  the predictor's copy of `q`; for interior `q` iff the two act values are equal
  (`pennies_interior_adviceEdt_iff`). Matching pennies (`mpPay`, win on mismatch):
  `EV(H) − EV(T) = (p−1)(2q−1)` (`penEV_mp_sub`), for `p < 1` approval iff `q = 1/2`
  (`mp_adviceEdt_iff`), `V_B = 2(1−p)q(1−q)` (`mp_value`), and at `p = 1` every mixture is
  vacuously ratifiable (`mp_adviceEdt_of_p_one`: every value is `0`).
* The tremble-limit values are computed through the one general lemma `limitVal_of_factor`
  (`nuPoly = t`, `payPoly = t·g`, `t ≠ 0` ⟹ `limitVal = g(0)`), which is what makes the
  boundary labels' values defined.

Finding (filed as F13): the C2 ledger's Mean-Demon precedent for the `2×2` tie is a conflation —
see `dp-firstperson-sc-findings.md`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-! ## T17(a): CEDT at self-transparent points -/

section cedt

variable (s : ι → State Ω K) (obs : ι → Finset Ω) (cf : Cf Ω K)
  (actEv : (d : ι) → acts d → Finset Ω) (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **P02-8′'s CEDT rule of record**: strict observation calibration (Definition 8) ∧
`T_CDT`-approval (Definition 18 at the counterfactual slot `cf`). "The chosen action must be the
best causal intervention, after taking into account (as evidence) the fact that we chose it": the
inner conditioning on the choice is done by calibration, the outer `argmax` is Definition 17's
total-domain causal evaluator, and "chosen ∈ argmax" is Definition 18's support condition.
Source: `sl-workflow/notes/repair/P02.md` P02-8′ ("= strict observation calibration ∧
`T_CDT`-approval at self-transparent points"); mandate T17(a)
Kind: D
Fidelity: exact (the self-transparency clause is `CEDTSelfTransparent`) -/
def CEDT : Prop := StrictOC s obs C B ∧ TCdt cf actEv C B

/-- **CEDT at self-transparent points**: `CEDT` with Appendix B item 2's `P_{s_d}(a) = C(d)(a)`
at every queried point — P02-8′'s domain clause made explicit.
Source: `P02.md` P02-8′ ("at self-transparent points"); [[decision-problems-v2]] Appendix B item 2
Kind: D
Fidelity: exact -/
def CEDTSelfTransparent : Prop :=
  CEDT s obs cf actEv C B ∧ ∀ d ∈ queried B, SelfTransparent s actEv C d

/-- **At recorded points CEDT is automatically at self-transparent points**: if `B` records at
every queried `d` for `C` (Definition 7) with `ν(O_d) > 0`, strict OC gives self-transparency
(`dp-calibration`'s `selfTransparent_of_recordsFor_strict`, Remark 3.6), so `CEDT` there is
`T_CDT`-approval at the calibrated state (P02-8′'s "there CEDT(R2-real) is the classical-CDT
fixed-point set").
Source: `P02.md` P02-8′ ("Where `P_{s_d}(a) = C(d)(a)` — Definition 7 recording (Remark 3.6) …");
[[decision-problems-v2]] Remark 3.6
Kind: C
Fidelity: exact
Hyps: (a) recording and `ν(O_d) > 0` at every queried point -/
theorem cedt_selfTransparent_of_recordsFor (h : CEDT s obs cf actEv C B)
    (hrec : ∀ d ∈ queried B, RecordsFor obs actEv C B d ∧ 0 < nu C B (obs d)) :
    CEDTSelfTransparent s obs cf actEv C B :=
  ⟨h, fun d hd => selfTransparent_of_recordsFor_strict obs actEv C B s (hrec d hd).1 (hrec d hd).2
    (h.1 d hd)⟩

end cedt

/-! ## The miniature's forcing referent and `CEDT(R2-real) = {2/3}` -/

/-- **The miniature with its live node forced to `a`**: the predictor still samples `s ∼ C(d)`,
the live draw is replaced by `a`. Its strict state at `⊤` is the forcing referent's value at `a`
(R2-real: single-instance forcing at the node-action-veridical live node, reach-weighted — on the
miniature the live nodes are the only node-action-veridical `d`-nodes and their reach weights are
`C(d)(s)`, so forcing the live node under every sample is R2-real; this identification is stated,
not proved in Lean).
Source: `sl-workflow/notes/repair/C1.md` vocabulary ("R2-real = reach-weighted single-instance
forcing `G_q(C, a)` averaged over the node-action-veridical `d`-nodes"); [[decision-problems-v2]]
Remark 4.3
Kind: D
Fidelity: variant: forcing realized as a tree (the live node deleted, its act fixed) -/
def miniForced (a : Act2) : Tree MiniW Unit (fun _ => Act2) ℚ :=
  .decision () fun s => .leaf (s, a) (miniPay s a)

/-- Leaf sums on the forced miniature. Source: none: infrastructure. Kind: L -/
theorem miniForced_sum {M : Type} [AddCommMonoid M] (a : Act2) (f : (miniForced a).Leaves → M) :
    ∑ ℓ, f ℓ = ∑ s, f ⟨s, ()⟩ := by
  unfold miniForced at f ⊢
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- The forcing referent's state at `a`: the strict state of `procQ q` on `miniForced a` at `⊤`.
Source: `C1.md` vocabulary (R2-real); mandate T17(a) ("the forcing `cf`")
Kind: D -/
noncomputable def miniForceState (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (a : Act2) : State MiniW ℚ :=
  calibratedState (procQ q h0 h1) (miniForced a) Finset.univ (nu_univ_pos _ _)

/-- **The forcing `cf` on the miniature** (R2-real), packaged on the act events. A local
stand-in for C1's R2-real forcing referent: [[STANDARDS]] §3's **(c)** — the identification of
the forced tree's strict state with C1's reach-weighted node average is stated in `miniForced`'s
docstring, not proved in Lean.
Source: `C1.md` vocabulary (R2-real); `P02.md` P02-8′
Kind: D
Fidelity: variant: (c) `miniForceCf` for R2-real -/
noncomputable def miniForceCf (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : Cf MiniW ℚ :=
  Cf.ofEvents miniActEv () (fun a => miniForceState q h0 h1 a)

/-- The live-draw events are distinct for distinct acts. Source: none: infrastructure. Kind: L -/
theorem miniActEv_injective : Function.Injective (miniActEv ()) := by
  intro a b h
  have hm : (a, a) ∈ miniActEv () a := by simp [miniActEv]
  rw [h] at hm
  simpa [miniActEv] using hm

/-- `V^a = 2(1 − q)` under the forcing referent, at every `q` (no guard: the forced act is certain).
Source: [[decision-problems-v2]] Remark 4.3 (`V(a) = 2(1−q)`); `P02.md` P02-8′
Kind: P -/
theorem miniForceCf_V_a (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (miniForceCf q h0 h1 (miniActEv () .a)).V (miniActEv () .a) = 2 * (1 - q) := by
  unfold miniForceCf
  rw [Cf.ofEvents_apply miniActEv () _ miniActEv_injective .a]
  unfold miniForceState
  rw [calibratedState_V, Finset.inter_univ]
  unfold paySum nu Tree.mass worldEv
  rw [Finset.sum_filter, Finset.sum_filter, miniForced_sum, miniForced_sum, Act2.sum_univ,
    Act2.sum_univ]
  simp [miniForced, miniActEv, miniPay, procQ]
  ring

/-- `V^b = q` under the forcing referent, at every `q`.
Source: [[decision-problems-v2]] Remark 4.3 (`V(b) = q`); `P02.md` P02-8′
Kind: P -/
theorem miniForceCf_V_b (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (miniForceCf q h0 h1 (miniActEv () .b)).V (miniActEv () .b) = q := by
  unfold miniForceCf
  rw [Cf.ofEvents_apply miniActEv () _ miniActEv_injective .b]
  unfold miniForceState
  rw [calibratedState_V, Finset.inter_univ]
  unfold paySum nu Tree.mass worldEv
  rw [Finset.sum_filter, Finset.sum_filter, miniForced_sum, miniForced_sum, Act2.sum_univ,
    Act2.sum_univ]
  simp [miniForced, miniActEv, miniPay, procQ]

/-- **`CEDT(R2-real) = {2/3}` on the miniature**: `procQ q` with its strict state is CEDT under the
forcing referent iff `q = 2/3`. The pure labels are *rejected* (`T_CDT` is total: at `q = 1`,
`V^b = 1 > 0 = V^a`; at `q = 0`, `V^a = 2 > 0 = V^b`), in contrast with `T_EDT`'s vacuous approval
of them (`miniature_tEdt_pure_a`, `miniature_tEdt_pure_b`) — P02-8′'s "contrast with `T_EDT`'s
vacuous approval of deterministic labels (Remark 3.9) is the post's point".
Source: `P02.md` P02-8′ ("CEDT(R2-real) is the classical-CDT fixed-point set"); mandate T17(a)
("CEDT(R2-real) = {⅔}")
Kind: P
Fidelity: variant: R2-real realized as the forced tree `miniForced` (the identification with C1's
reach-weighted node average is stated, not proved)
Hyps: (a) `0 ≤ q ≤ 1`; (c) `miniForceCf` stands in for C1's R2-real forcing referent -/
theorem miniature_cedt_iff (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    CEDT (fun _ => miniState q h0 h1) miniObs (miniForceCf q h0 h1) miniActEv (procQ q h0 h1)
      miniature ↔ q = 2 / 3 := by
  constructor
  · rintro ⟨_, hT⟩
    have hq := hT () miniature_queried
    rcases lt_or_eq_of_le h0 with hpos | hzero
    · have ha := (mem_argmaxFull _ _).mp (hq .a (by simp [procQ, hpos])) .b
      simp only [miniForceCf_V_a, miniForceCf_V_b] at ha
      rcases lt_or_eq_of_le h1 with hlt | hone
      · have hb := (mem_argmaxFull _ _).mp (hq .b (by simp [procQ]; linarith)) .a
        simp only [miniForceCf_V_a, miniForceCf_V_b] at hb
        linarith
      · subst hone; linarith
    · subst hzero
      have hb := (mem_argmaxFull _ _).mp (hq .b (by simp [procQ])) .a
      simp only [miniForceCf_V_a, miniForceCf_V_b] at hb
      linarith
  · rintro rfl
    refine ⟨miniature_strictOC _ _ _, ?_⟩
    intro d _ a _
    cases d
    rw [mem_argmaxFull]
    intro b
    cases a <;> cases b <;> simp only [miniForceCf_V_a, miniForceCf_V_b] <;> norm_num

/-! ## T17(b): matching pennies and the `2×2` tie -/

/-- Pennies worlds `(act, guess)`. Source: `P03.md` P03-6. Kind: D -/
abbrev PenW : Type := Act2 × Act2

/-- **The pennies tree** `pennies p u`: the agent draws `a ∼ C(d)`; the predictor's independent
sample `b ∼ C(d)` (a second `d`-node); then a draw-keyed chance node — with probability `p` the
guess is the draw `a`, else the sample `b`; leaf world `(a, guess)`, payoff `u a guess`.
Shape disclosure (fidelity: variant): the sample is drawn on every path (`#_d = 2` everywhere)
rather than only on the independent branch; the law of `(act, guess)` is the source's.
Source: `P03.md` P03-6 ("with probability `p` the guess is the realized draw (a draw-keyed
post-draw chance node), else an independent sample of `C(d)`"); mandate T17(b)
Kind: D
Fidelity: variant: the independent sample is drawn on every path (uniform leaf type) -/
def pennies (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (u : Act2 → Act2 → ℚ) :
    Tree PenW Unit (fun _ => Act2) ℚ :=
  .decision () fun a => .decision () fun b =>
    .chance 2 (FinDistr.coin p h0 h1) fun i =>
      .leaf (a, if i = 0 then a else b) (u a (if i = 0 then a else b))

/-- `O = ⊤` on the pennies tree. Source: `P03.md` P03-6 (`O_d`-conditioned at `⊤`). Kind: D -/
def penObs : Unit → Finset PenW := fun _ => Finset.univ

/-- Act events `{act = a}` (the agent's draw, the first coordinate).
Source: `P03.md` P03-6
Kind: D -/
def penActEv (_ : Unit) (a : Act2) : Finset PenW := Finset.univ.filter fun w => w.1 = a

/-- **The evidential act value against the predictor's copy of `q`**:
`EV(a) = p·u(a,a) + (1−p)·(q·u(a,H) + (1−q)·u(a,T))`.
Source: `P03.md` P03-6 (`EV(H) = (1−p)(1−q)`, `EV(T) = (1−p)q` for matching pennies)
Kind: D -/
def penEV (p : ℚ) (u : Act2 → Act2 → ℚ) (q : ℚ) (a : Act2) : ℚ :=
  p * u a a + (1 - p) * (q * u a .a + (1 - q) * u a .b)

/-- **Matching pennies**: the agent wins (`1`) on a mismatch with the guess, else `0`.
Source: `P03.md` P03-6
Kind: D -/
def mpPay : Act2 → Act2 → ℚ := fun a b => if a = b then 0 else 1

section pennies

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (u : Act2 → Act2 → ℚ)

/-- Leaf sums on the pennies tree. Source: none: infrastructure. Kind: L -/
theorem pennies_sum {M : Type} [AddCommMonoid M] (f : (pennies p h0 h1 u).Leaves → M) :
    ∑ ℓ, f ℓ = ∑ a, ∑ b, ∑ i : Fin 2, f ⟨a, b, i, ()⟩ := by
  unfold pennies at f ⊢
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- The world at a leaf. Source: none: infrastructure. Kind: L -/
theorem pennies_world (a b : Act2) (i : Fin 2) :
    world (pennies p h0 h1 u) ⟨a, b, i, ()⟩ = (a, if i = 0 then a else b) := by
  unfold pennies; simp

/-- The payoff at a leaf. Source: none: infrastructure. Kind: L -/
theorem pennies_payoff (a b : Act2) (i : Fin 2) :
    payoff (pennies p h0 h1 u) ⟨a, b, i, ()⟩ = u a (if i = 0 then a else b) := by
  unfold pennies; simp

/-- The run law at a leaf. Source: none: infrastructure. Kind: L -/
theorem pennies_leafLaw (C : Proc Unit (fun _ => Act2) ℚ) (a b : Act2) (i : Fin 2) :
    leafLaw C (pennies p h0 h1 u) ⟨a, b, i, ()⟩ = (C ()).w a * ((C ()).w b * (![p, 1 - p] i * 1)) := by
  unfold pennies
  simp only [leafLaw_decision, leafLaw_chance, leafLaw_leaf]
  rfl

/-- The tremble polynomial at a leaf. Source: none: infrastructure. Kind: L -/
theorem pennies_leafLawPoly (C : Proc Unit (fun _ => Act2) ℚ) (a b : Act2) (i : Fin 2) :
    leafLawPoly C (pennies p h0 h1 u) ⟨a, b, i, ()⟩ =
      trembleW C () a * (trembleW C () b * (Polynomial.C (![p, 1 - p] i) * 1)) := by
  unfold pennies
  simp only [leafLawPoly]
  rfl

/-- `d` is queried on the pennies tree. Source: none: infrastructure. Kind: L -/
theorem pennies_queried : () ∈ queried (pennies p h0 h1 u) := by
  unfold pennies; simp [queried_decision]

/-- The strict state of `procQ q` at `⊤` is strictly observation-calibrated on the pennies tree.
Source: `P03.md` P03-6 ("strictly calibrated")
Kind: L -/
theorem pennies_strictOC (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    StrictOC (fun _ => calibratedState (procQ q hq0 hq1) (pennies p h0 h1 u) Finset.univ
      (nu_univ_pos _ _)) penObs (procQ q hq0 hq1) (pennies p h0 h1 u) :=
  fun _ _ => strictOCAt_calibratedState penObs _ _ _ () _ rfl

end pennies

/-- `trembleW a + trembleW b = 1` on a two-action point. Source: none: infrastructure. Kind: L -/
theorem trembleW_act2_add (C : Proc Unit (fun _ => Act2) ℚ) :
    trembleW C () .a + trembleW C () .b = 1 := by
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hc : (Fintype.card Act2 : ℚ) = 2 := by
    rw [Fintype.card, Act2.univ_eq, Finset.card_pair (by decide)]; norm_num
  simp only [trembleW, hc]
  ext n
  simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_one]
  rcases n with _ | _ | n
  · simp; linarith
  · simp; linarith
  · simp

/-- `(trembleW C d a).coeff 0 = C(d)(a)`. Source: none: infrastructure. Kind: L -/
theorem trembleW_coeff_zero [∀ d, Nonempty (acts d)] (C : Proc ι acts K) (d : ι) (a : acts d) :
    (trembleW C d a).coeff 0 = (C d).w a := by
  simp [trembleW, Polynomial.coeff_add, Polynomial.coeff_C]

/-- `nuPoly` of `⊤` is non-zero (its value at `ε = 1` is `1`). Source: none: infrastructure.
Kind: L -/
theorem nuPoly_univ_ne_zero [∀ d, Nonempty (acts d)] (C : Proc ι acts K) (B : Tree Ω ι acts K) :
    nuPoly C B Finset.univ ≠ 0 := by
  intro h
  have := eval_nuPoly C B Finset.univ 1 zero_le_one le_rfl
  rw [h, Polynomial.eval_zero, nu_univ] at this
  exact zero_ne_one this

/-- **The tremble limit of a factored pair**: if `nuPoly Y = t` and `payPoly Y = t · g` with
`t ≠ 0`, then `limitVal Y = g(0)` — the coefficient of `ε^k` (`k` the order of `t`) in `t · g` is
`t_k · g_0`. This is what makes the act values of null acts defined: `t` carries the vanishing
order, `g` the value.
Source: [[decision-problems-v2]] Remark 3.9 (advice stance); `calibration.md` D4
Kind: L -/
theorem limitVal_of_factor [∀ d, Nonempty (acts d)] (C : Proc ι acts K) (B : Tree Ω ι acts K)
    (Y : Finset Ω) (t g : Polynomial K) (ht : t ≠ 0) (hn : nuPoly C B Y = t)
    (hp : payPoly C B Y = t * g) : limitVal C B Y = g.coeff 0 := by
  unfold limitVal
  rw [hn, hp]
  have hk : t.coeff t.natTrailingDegree ≠ 0 :=
    Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr ht
  have hmul : (t * g).coeff t.natTrailingDegree = t.coeff t.natTrailingDegree * g.coeff 0 := by
    rw [Polynomial.coeff_mul, Finset.sum_eq_single (t.natTrailingDegree, 0)]
    · intro x hx hne
      have hsum := Finset.mem_antidiagonal.mp hx
      by_cases hlt : x.1 < t.natTrailingDegree
      · rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt, zero_mul]
      · exfalso
        apply hne
        have h1 : x.1 = t.natTrailingDegree := by omega
        have h2 : x.2 = 0 := by omega
        exact Prod.ext h1 h2
    · intro h
      exact absurd (Finset.mem_antidiagonal.mpr (by simp)) h
  rw [hmul, mul_div_cancel_left₀ _ hk]

section penniesLimit

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (u : Act2 → Act2 → ℚ)

/-- `nuPoly` of an act event on the pennies tree is that act's tremble weight.
Source: none: infrastructure. Kind: L -/
theorem nuPoly_pennies (C : Proc Unit (fun _ => Act2) ℚ) (a : Act2) :
    nuPoly C (pennies p h0 h1 u) (penActEv () a ∩ penObs ()) = trembleW C () a := by
  have hs := trembleW_act2_add C
  have hp' : (Polynomial.C (1 - p) : Polynomial ℚ) = 1 - Polynomial.C p := by
    rw [Polynomial.C_sub, Polynomial.C_1]
  rw [penObs, Finset.inter_univ, nuPoly_eq_sum, pennies_sum]
  simp only [pennies_world, pennies_leafLawPoly, penActEv, Finset.mem_filter, Finset.mem_univ,
    true_and]
  simp only [Act2.sum_univ, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, hp']
  cases a
  · simp
    linear_combination (trembleW C () Act2.a) * hs
  · simp
    linear_combination (trembleW C () Act2.b) * hs

/-- `payPoly` of an act event on the pennies tree, factored by that act's tremble weight.
Source: none: infrastructure. Kind: L -/
theorem payPoly_pennies (C : Proc Unit (fun _ => Act2) ℚ) (a : Act2) :
    payPoly C (pennies p h0 h1 u) (penActEv () a ∩ penObs ()) =
      trembleW C () a *
        ∑ b, trembleW C () b * Polynomial.C (p * u a a + (1 - p) * u a b) := by
  rw [penObs, Finset.inter_univ, payPoly_eq_sum, pennies_sum]
  simp only [pennies_world, pennies_payoff, pennies_leafLawPoly, penActEv, Finset.mem_filter,
    Finset.mem_univ, true_and]
  simp only [Act2.sum_univ, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Polynomial.C_add, Polynomial.C_mul]
  cases a <;> simp <;> ring

/-- **The tremble-limit act values on the pennies tree are `penEV` at every `q ∈ [0, 1]`**
(defined at the boundary labels, where the strict values are not).
Source: `P03.md` P03-6; [[decision-problems-v2]] Remark 3.9
Kind: P
Fidelity: exact (limit taken algebraically, `dp-calibration`'s `limitVal`) -/
theorem limitVal_pennies (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (a : Act2) :
    limitVal (procQ q hq0 hq1) (pennies p h0 h1 u) (penActEv () a ∩ penObs ()) =
      penEV p u q a := by
  rw [limitVal_of_factor _ _ _ (trembleW (procQ q hq0 hq1) () a)
    (∑ b, trembleW (procQ q hq0 hq1) () b * Polynomial.C (p * u a a + (1 - p) * u a b))
    (trembleW_ne_zero _ _ _) (nuPoly_pennies p h0 h1 u _ a) (payPoly_pennies p h0 h1 u _ a)]
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_mul_C, trembleW_coeff_zero, Act2.sum_univ, procQ, FinDistr.act2_a,
    FinDistr.act2_b]
  unfold penEV
  ring

/-- **P03-6 / dp-sl-2-048, the `2×2` tie as a best-reply condition**: for every skill `p` and
payoff table `u`, the label `q` is `T_EDT`-approved in the tremble limit (D4, `AdviceEdt`) iff
every act in its support maximizes `EV(·) = p·u(·,·) + (1−p)·∑_b q_b u(·, b)` — the agent's best
reply to the predictor's copy of `q`, the symmetric game's fixed-point condition.
Source: `L2.md:163` (ii) ("the unique strictly-calibrated-and-tremble-limit-approved mixture in a
`2×2` zero-sum-against-predictor table is the Nash mixture"); `P03.md` P03-6; mandate T17(b)
Kind: P
Fidelity: exact (for the `T_EDT` reading; the strict state at `⊤` is `pennies_strictOC`)
Hyps: (a) `0 ≤ q ≤ 1` -/
theorem pennies_adviceEdt_iff (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    AdviceEdt penObs penActEv (procQ q hq0 hq1) (pennies p h0 h1 u) ↔
      ∀ a, 0 < (procQ q hq0 hq1 ()).w a → ∀ b, penEV p u q b ≤ penEV p u q a := by
  constructor
  · intro h a ha b
    have := (h () (pennies_queried p h0 h1 u) (nuPoly_univ_ne_zero _ _)
      ⟨.a, by rw [nuPoly_pennies]; exact trembleW_ne_zero _ _ _⟩ a ha).2 b
      (by rw [nuPoly_pennies]; exact trembleW_ne_zero _ _ _)
    rwa [limitVal_pennies, limitVal_pennies] at this
  · intro h d _ _ _ a ha
    cases d
    refine ⟨by rw [nuPoly_pennies]; exact trembleW_ne_zero _ _ _, fun b _ => ?_⟩
    rw [limitVal_pennies, limitVal_pennies]
    exact h a ha b

/-- **Interior labels are approved iff the two act values are equal** (the tie).
Source: `P03.md` P03-6 ("unique tie"); `L2.md:163` (ii)
Kind: P
Hyps: (a) `0 < q < 1` -/
theorem pennies_interior_adviceEdt_iff (q : ℚ) (hq0 : 0 < q) (hq1 : q < 1) :
    AdviceEdt penObs penActEv (procQ q hq0.le hq1.le) (pennies p h0 h1 u) ↔
      penEV p u q .a = penEV p u q .b := by
  rw [pennies_adviceEdt_iff]
  constructor
  · intro h
    have ha := h .a (by simp [procQ, hq0]) .b
    have hb := h .b (by simp [procQ]; linarith) .a
    exact le_antisymm hb ha
  · intro h a _ b
    cases a <;> cases b <;> simp only [h, le_refl]

end penniesLimit

/-! ### Matching pennies -/

/-- `EV(H) = (1−p)(1−q)`, `EV(T) = (1−p)q` for matching pennies. Source: `P03.md` P03-6. Kind: L -/
theorem penEV_mp (p q : ℚ) :
    penEV p mpPay q .a = (1 - p) * (1 - q) ∧ penEV p mpPay q .b = (1 - p) * q := by
  unfold penEV mpPay
  constructor <;> simp <;> ring

/-- **`EV(H) − EV(T) = (p − 1)(2q − 1)`**. Source: `P03.md` P03-6 ("difference `(p−1)(2q−1)`").
Kind: P -/
theorem penEV_mp_sub (p q : ℚ) :
    penEV p mpPay q .a - penEV p mpPay q .b = (p - 1) * (2 * q - 1) := by
  obtain ⟨ha, hb⟩ := penEV_mp p q
  rw [ha, hb]; ring

/-- **Matching pennies against a predictor of skill `p < 1`: the strictly calibrated label `q` is
`T_EDT`-approved in the tremble limit iff `q = 1/2`** — the 50–50 label is the evaluator's unique
fixed point.
Source: `P03.md` P03-6 ("the 50–50 label is every `O_d`-conditioned evaluator's fixed point under
Definition 6 for `p < 1`"); mandate T17(b)
Kind: P
Fidelity: exact
Hyps: (a) `p < 1`, (a) `0 ≤ q ≤ 1` -/
theorem mp_adviceEdt_iff (p : ℚ) (h0 : 0 ≤ p) (hp : p < 1) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    AdviceEdt penObs penActEv (procQ q hq0 hq1) (pennies p h0 hp.le mpPay) ↔ q = 1 / 2 := by
  rw [pennies_adviceEdt_iff]
  obtain ⟨ha, hb⟩ := penEV_mp p q
  constructor
  · intro h
    rcases lt_or_eq_of_le hq0 with hpos | hzero
    · have h1 := h .a (by simp [procQ, hpos]) .b
      rw [ha, hb] at h1
      rcases lt_or_eq_of_le hq1 with hlt | hone
      · have h2 := h .b (by simp [procQ]; linarith) .a
        rw [ha, hb] at h2
        nlinarith
      · subst hone; nlinarith
    · subst hzero
      have h2 := h .b (by simp [procQ]) .a
      rw [ha, hb] at h2
      nlinarith
  · rintro rfl
    intro a _ b
    cases a <;> cases b <;> simp only [ha, hb] <;> norm_num

/-- **At `p = 1` every mixture is vacuously ratifiable**: both act values are `0`.
Source: `P03.md` P03-6 ("At `p = 1` every value is `0` and every mixture is vacuously ratifiable")
Kind: N+ -/
theorem mp_adviceEdt_of_p_one (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    AdviceEdt penObs penActEv (procQ q hq0 hq1) (pennies 1 zero_le_one le_rfl mpPay) := by
  rw [pennies_adviceEdt_iff]
  obtain ⟨ha, hb⟩ := penEV_mp 1 q
  intro a _ b
  cases a <;> cases b <;> simp only [ha, hb] <;> norm_num

/-- **`V_B(q) = 2(1 − p) q (1 − q)`** for matching pennies, maximal at `q = 1/2`.
Source: `P03.md` P03-6 (`V_B = 2(1−p)q(1−q)`, maximal there)
Kind: P
Fidelity: exact -/
theorem mp_value (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    value (procQ q hq0 hq1) (pennies p h0 h1 mpPay) = 2 * (1 - p) * q * (1 - q) := by
  unfold value
  rw [pennies_sum]
  simp only [pennies_leafLaw, pennies_payoff]
  simp only [Act2.sum_univ, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, procQ, FinDistr.act2_a, FinDistr.act2_b, mpPay]
  simp
  ring

end Cleanroom.Decision.DpFirstpersonSc
