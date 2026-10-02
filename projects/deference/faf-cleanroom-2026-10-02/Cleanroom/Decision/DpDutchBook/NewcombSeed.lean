import Cleanroom.Decision.DpDutchBook.Newcomb
import Cleanroom.Found.DpCoreTree.Seed

/-!
# T3, the 6′ side: opaque Newcomb under the shared seed — the roles reverse

Under Definition 6′ (`leafLaw'`/`nu'`/`value'`, `dp-core-tree`'s `Seed.lean`) the predictor's
sample and the live draw are one draw, so on `opaqueNewcomb p L S` the run law is
`μ'(s, i, l) = C(d)(s) · coin(i) · [s = l]` (`opaque_leafLaw'`). Consequences, all with
`(p, L, S, q)` free:

* **Conditioning under 6′ is the deviation value**: `e'(one) = Lp`, `e'(two) = L(1−p) + S`
  (`opaqueE'_a/_b`) — exactly the R1-state values `V'(C[d ↦ δ_a])` (`opaqueR1State'_a/_b`,
  `opaqueE'_eq_r1State'`), so the deviation referent is **unbookable** under 6′
  (`opaque_gap'_r1`: `Δ' = 0`).
* **The forcing-type value under 6′** is the *do*-CDT construal of SE-1(d): the seed still routes
  the fill (`s ∼ C(d)`), the real node is forced to `a` — the explicit closed form
  `∑_{s,i} C(d)(s)·coin(i)·pay(fill(s,i), a)` (`opaqueDoCdt'`), which equals Definition 6's
  conditioning `e(a)` (`opaqueDoCdt'_eq_opaqueE`), and is **bitten** at
  `Δ'_{do}(one) = Δ'_{do}(two) = q·L·(1−q)·(2p−1)` for `p ≥ ½` (`opaque_gap'_do_a/_b`).
* **The inversion** (`opaque_inversion`): under Definition 6 the deviation referent is bitten at
  `qL(1−q)(2p−1)` and the forcing referent spared; under 6′ the deviation referent is spared and
  the forcing (do) referent bitten at the same magnitude. At the deterministic labels the taken
  act has `Δ' = 0` under both cfs (`opaque_gap'_fixed`).
* S12's "`q(1−q) − 2δ` at `p = 1`" is the `L = 1` normalisation of `qL(1−q)` (findings F-F).

`paySumSeed`/`condExpSeed` are local (`dp-referents-cdt` owns the general `paySum'`; this file
does not import it). Fidelity for every 6′ row: *variant: the forcing referent under 6′ is
SE-1(d)'s definable-not-intrinsic construal*; the T2 extension theorems are Definition-6 objects
and are not re-proved under 6′ — the 6′ "book" is carried by these gap closed forms.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpDutchBook

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-- The shared-seed payoff mass `𝔼_{μ'}[r · 1_X]` (local; `dp-referents-cdt` owns the general
`paySum'`). Source: `seeds.md` Definition 6′; mandate T3. Kind: D -/
def paySumSeed (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) : K :=
  ∑ ℓ ∈ worldEv B X, leafLaw' C B ℓ * payoff B ℓ

/-- The shared-seed conditional act value `𝔼_{μ'}[r ∣ X] = paySumSeed / ν'` (junk `0` at
`ν' = 0`; every headline guards it). Source: `seeds.md` Definition 6′; mandate T3. Kind: D -/
noncomputable def condExpSeed (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) : K :=
  paySumSeed C B X / nu' C B X

/-- `paySumSeed` as a sum with an indicator. Source: none: infrastructure. Kind: L -/
theorem paySumSeed_eq_sum_ite (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) :
    paySumSeed C B X = ∑ ℓ, if world B ℓ ∈ X then leafLaw' C B ℓ * payoff B ℓ else 0 := by
  unfold paySumSeed worldEv; rw [Finset.sum_filter]

/-- `nu'` as a sum with an indicator. Source: none: infrastructure. Kind: L -/
theorem nu'_eq_sum_ite (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) :
    nu' C B X = ∑ ℓ, if world B ℓ ∈ X then leafLaw' C B ℓ else 0 := by
  unfold nu' worldEv; rw [Finset.sum_filter]

section opaqueSeed

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) (C : Proc Unit (fun _ => Act2) ℚ)

/-- **The shared-seed run law on opaque Newcomb**: `μ'(s, i, l) = C(d)(s) · coin(i) · [s = l]` —
the predictor's sample is the live draw.
Source: `seeds.md` Definition 6′; `repair/C2.md` C2-16′ ("under the shared seed"); mandate T3
Kind: P
Fidelity: exact -/
theorem opaque_leafLaw' (s : Act2) (i : Fin 2) (l : Act2) :
    leafLaw' C (opaqueNewcomb p h0 h1 L S) ⟨s, ⟨i, ⟨l, ()⟩⟩⟩ =
      (C ()).w s * (FinDistr.coin p h0 h1).w i * (if s = l then 1 else 0) := by
  unfold leafLaw' opaqueNewcomb
  rw [leafLawSeed_decision_of_none C rfl, leafLawSeed_chance,
    leafLawSeed_decision_of_some C (a' := s) (by simp)]
  simp only [leafLawSeed_leaf]
  split_ifs <;> ring

/-- `ν'(act = a) = C(d)(a)` on opaque Newcomb. Source: none: infrastructure. Kind: L -/
theorem opaque_nu'_act (a : Act2) :
    nu' C (opaqueNewcomb p h0 h1 L S) (opaqueActEv () a) = (C ()).w a := by
  rw [nu'_eq_sum_ite, opaque_sum]
  simp only [opaque_leafLaw']
  have hc := (FinDistr.coin p h0 h1).sum_one
  rw [Fin.sum_univ_two] at hc
  cases a <;> simp [Act2.sum_univ, Fin.sum_univ_two, opaqueNewcomb, opaqueActEv] <;>
    linear_combination (C ()).w _ * hc

/-- `𝔼'[r · 1_{one}] = q · L · p` on opaque Newcomb (the seed fills the box according to the
live act). Source: none: infrastructure. Kind: L -/
theorem opaque_paySumSeed_a :
    paySumSeed C (opaqueNewcomb p h0 h1 L S) (opaqueActEv () .a) = (C ()).w .a * (L * p) := by
  rw [paySumSeed_eq_sum_ite, opaque_sum]
  simp only [opaque_leafLaw']
  simp [Act2.sum_univ, Fin.sum_univ_two, opaqueNewcomb, opaqueActEv, opaquePay, opaqueFill,
    FinDistr.coin]
  ring

/-- `𝔼'[r · 1_{two}] = (1−q) · (L(1−p) + S)` on opaque Newcomb. Source: none: infrastructure.
Kind: L -/
theorem opaque_paySumSeed_b :
    paySumSeed C (opaqueNewcomb p h0 h1 L S) (opaqueActEv () .b) =
      (C ()).w .b * (L * (1 - p) + S) := by
  rw [paySumSeed_eq_sum_ite, opaque_sum]
  simp only [opaque_leafLaw']
  simp [Act2.sum_univ, Fin.sum_univ_two, opaqueNewcomb, opaqueActEv, opaquePay, opaqueFill,
    FinDistr.coin]
  ring

/-- The strictly calibrated act value under 6′: `e'(a) = 𝔼'[r ∣ a ∧ O_d]`.
Source: `repair/C2.md` C2-16′ ("under the shared seed … conditioning"); mandate T3
Kind: D
Fidelity: variant: Definition 6′'s run law -/
noncomputable def opaqueE' (a : Act2) : ℚ :=
  condExpSeed C (opaqueNewcomb p h0 h1 L S) (opaqueActEv () a ∩ opaqueObs ())

/-- **`e'(one) = Lp`** under 6′ at a positive one-box weight.
Source: C2-16′; S12; mandate T3 (6′ side)
Kind: P
Fidelity: variant: 6′
Hyps: (a) `0 < q` -/
theorem opaqueE'_a (hq : 0 < (C ()).w .a) : opaqueE' p h0 h1 L S C .a = L * p := by
  unfold opaqueE' condExpSeed
  rw [opaqueObs, Finset.inter_univ, opaque_paySumSeed_a, opaque_nu'_act]
  field_simp

/-- **`e'(two) = L(1−p) + S`** under 6′ at a positive two-box weight.
Source: C2-16′; mandate T3 (6′ side)
Kind: P
Fidelity: variant: 6′
Hyps: (a) `0 < 1 − q` -/
theorem opaqueE'_b (hq : 0 < (C ()).w .b) : opaqueE' p h0 h1 L S C .b = L * (1 - p) + S := by
  unfold opaqueE' condExpSeed
  rw [opaqueObs, Finset.inter_univ, opaque_paySumSeed_b, opaque_nu'_act]
  field_simp

/-- The deviation referent R1-state under 6′: `V'(C[d ↦ δ_a])`.
Source: C2-16′; mandate §3.2 (primed forms through `value'`)
Kind: D -/
def opaqueR1State' (a : Act2) : ℚ := value' (C.deviatePure () a) (opaqueNewcomb p h0 h1 L S)

/-- **`R1-state'(one) = Lp`**: the deterministic one-boxer's shared-seed value (equal to its
Definition-6 value — a deterministic procedure has one run law).
Source: C2-16′; mandate T3
Kind: P
Fidelity: exact -/
theorem opaqueR1State'_a : opaqueR1State' p h0 h1 L S C .a = L * p := by
  unfold opaqueR1State' value'
  rw [opaque_sum]
  simp only [opaque_leafLaw']
  rw [Proc.deviatePure, deviate_unit]
  simp [Fin.sum_univ_two, opaqueNewcomb, opaquePay, opaqueFill, FinDistr.coin, FinDistr.pure]
  ring

/-- **`R1-state'(two) = L(1−p) + S`**.
Source: C2-16′; mandate T3
Kind: P
Fidelity: exact -/
theorem opaqueR1State'_b : opaqueR1State' p h0 h1 L S C .b = L * (1 - p) + S := by
  unfold opaqueR1State' value'
  rw [opaque_sum]
  simp only [opaque_leafLaw']
  rw [Proc.deviatePure, deviate_unit]
  simp [Fin.sum_univ_two, opaqueNewcomb, opaquePay, opaqueFill, FinDistr.coin, FinDistr.pure]
  ring

/-- **Under 6′ conditioning is the deviation value**: `e'(a) = R1-state'(a)` at every positive
act (S9's agreement, now for the deviation referent).
Source: `repair/C2.md` C2-16′ ("under the shared seed the deviation value equals
conditioning"); mandate T3 (6′ side)
Kind: C
Fidelity: variant: 6′
Hyps: (a) `0 < C(d)(a)` -/
theorem opaqueE'_eq_r1State' (a : Act2) (hq : 0 < (C ()).w a) :
    opaqueE' p h0 h1 L S C a = opaqueR1State' p h0 h1 L S C a := by
  cases a
  · rw [opaqueE'_a p h0 h1 L S C hq, opaqueR1State'_a]
  · rw [opaqueE'_b p h0 h1 L S C hq, opaqueR1State'_b]

/-- **The forcing-type value under 6′, do-CDT construal (SE-1(d))**: the seed still routes the
fill (`s ∼ C(d)`), the real node is forced to `a`:
`∑_{s,i} C(d)(s) · coin(i) · pay(fill(s, i), a)`. An explicit closed form — definable from the
tree, not an intrinsic run-law quantity of 6′ (the construal is disclosed, not derived).
Source: `cf-workflow/phase2-notes/repair/seeds.md` SE-1(d); `repair/C2.md` C2-16′ ("the
forcing-type value … bitten under 6′"); mandate T3
Kind: D
Fidelity: variant: the forcing referent under 6′ is SE-1(d)'s definable-not-intrinsic construal -/
def opaqueDoCdt' (a : Act2) : ℚ :=
  ∑ s : Act2, ∑ i : Fin 2,
    (C ()).w s * (FinDistr.coin p h0 h1).w i * opaquePay L S (opaqueFill s i, a)

/-- `do(one) = L(pq + (1−p)(1−q))`. Source: SE-1(d); mandate T3. Kind: P. Fidelity: variant -/
theorem opaqueDoCdt'_a :
    opaqueDoCdt' p h0 h1 L S C .a = L * (p * (C ()).w .a + (1 - p) * (C ()).w .b) := by
  unfold opaqueDoCdt'
  simp [Act2.sum_univ, Fin.sum_univ_two, opaquePay, opaqueFill, FinDistr.coin]
  ring

/-- `do(two) = L(pq + (1−p)(1−q)) + S`. Source: SE-1(d); mandate T3. Kind: P. Fidelity: variant -/
theorem opaqueDoCdt'_b :
    opaqueDoCdt' p h0 h1 L S C .b = L * (p * (C ()).w .a + (1 - p) * (C ()).w .b) + S := by
  unfold opaqueDoCdt'
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  simp [Act2.sum_univ, Fin.sum_univ_two, opaquePay, opaqueFill, FinDistr.coin]
  linear_combination S * hs

/-- **The do-CDT value under 6′ is Definition 6's conditioning** `e(a)` at every positive act:
the forcing-type referent of one semantics is the conditioning value of the other.
Source: C2-16′/C2-17′ (the inversion); mandate T3
Kind: C
Fidelity: variant: 6′ do-construal vs Definition-6 `condExp`
Hyps: (a) `0 < C(d)(a)` -/
theorem opaqueDoCdt'_eq_opaqueE (a : Act2) (hq : 0 < (C ()).w a) :
    opaqueDoCdt' p h0 h1 L S C a = opaqueE p h0 h1 L S C a := by
  cases a
  · rw [opaqueDoCdt'_a, opaqueE_a p h0 h1 L S C hq]
  · rw [opaqueDoCdt'_b, opaqueE_b p h0 h1 L S C hq]

/-! ### The gaps under 6′ -/

/-- **The deviation referent is unbookable under 6′**: `Δ'_{R1}(a) = 0` at every positive act.
Source: C2-16′ ("under the shared seed … the deviation referent … is spared"); S12; mandate T3
Kind: P
Fidelity: variant: 6′
Hyps: (a) `0 < C(d)(a)` -/
theorem opaque_gap'_r1 (a : Act2) (hq : 0 < (C ()).w a) :
    bookGap (C ()) (opaqueR1State' p h0 h1 L S C) (opaqueE' p h0 h1 L S C) a = 0 := by
  unfold bookGap
  rw [opaqueE'_eq_r1State' p h0 h1 L S C a hq, sub_self, abs_zero, mul_zero]

/-- **The do-CDT referent is bitten under 6′ at `Δ'(one) = q·L·(1−q)·(2p−1)`** for `p ≥ ½`,
`L ≥ 0` — the same magnitude as Definition 6's R1 gap (`opaque_gap_r1_a`), now on the forcing
side. At `p = 1` this is `qL(1−q)`: S12's "`q(1−q)`" is the `L = 1` normalisation (F-F).
Source: C2-16′; S12 (`sl-defensible-claims.md` lines 119–122); mandate T3
Kind: P
Fidelity: variant: the forcing referent under 6′ is SE-1(d)'s construal
Hyps: (a) `0 < q`, `½ ≤ p`, `0 ≤ L` -/
theorem opaque_gap'_do_a (hq : 0 < (C ()).w .a) (hp : 1 / 2 ≤ p) (hL : 0 ≤ L) :
    bookGap (C ()) (opaqueDoCdt' p h0 h1 L S C) (opaqueE' p h0 h1 L S C) .a =
      (C ()).w .a * L * (1 - (C ()).w .a) * (2 * p - 1) := by
  unfold bookGap
  rw [opaqueDoCdt'_a, opaqueE'_a p h0 h1 L S C hq]
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  have ha1 : (C ()).w .a ≤ 1 := by linarith [(C ()).nonneg .b]
  rw [hb]
  have hnn : 0 ≤ L * (1 - (C ()).w .a) * (2 * p - 1) := by
    apply mul_nonneg (mul_nonneg hL (by linarith)); linarith
  have : L * (p * (C ()).w .a + (1 - p) * (1 - (C ()).w .a)) - L * p =
      -(L * (1 - (C ()).w .a) * (2 * p - 1)) := by ring
  rw [this, abs_neg, abs_of_nonneg hnn]
  ring

/-- **`Δ'(two) = q·L·(1−q)·(2p−1)`** for the do-CDT referent under 6′ (`p ≥ ½`, `L ≥ 0`).
Source: C2-16′; mandate T3
Kind: P
Fidelity: variant: as `opaque_gap'_do_a`
Hyps: (a) `0 < 1 − q`, `½ ≤ p`, `0 ≤ L` -/
theorem opaque_gap'_do_b (hq : 0 < (C ()).w .b) (hp : 1 / 2 ≤ p) (hL : 0 ≤ L) :
    bookGap (C ()) (opaqueDoCdt' p h0 h1 L S C) (opaqueE' p h0 h1 L S C) .b =
      (C ()).w .a * L * (1 - (C ()).w .a) * (2 * p - 1) := by
  unfold bookGap
  rw [opaqueDoCdt'_b, opaqueE'_b p h0 h1 L S C hq]
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  have ha0 : 0 ≤ (C ()).w .a := (C ()).nonneg .a
  rw [hb] at hq ⊢
  have hnn : 0 ≤ L * (C ()).w .a * (2 * p - 1) := by
    apply mul_nonneg (mul_nonneg hL ha0); linarith
  have : L * (p * (C ()).w .a + (1 - p) * (1 - (C ()).w .a)) + S - (L * (1 - p) + S) =
      L * (C ()).w .a * (2 * p - 1) := by ring
  rw [this, abs_of_nonneg hnn]
  ring

/-- **At the deterministic labels the taken act has `Δ' = 0` under both 6′ cfs** (the deviation
and the do-CDT referent): nothing is booked at either fixed point under the shared seed either.
Source: P12-5 ("at opaque Newcomb's two deterministic fixed points … the taken act has `Δ = 0`
under both semantics"); mandate T3
Kind: P
Fidelity: variant: 6′
Hyps: (a) `½ ≤ p`, `0 ≤ L` -/
theorem opaque_gap'_fixed (hp : 1 / 2 ≤ p) (hL : 0 ≤ L) :
    ((C ()).w .a = 1 →
      bookGap (C ()) (opaqueR1State' p h0 h1 L S C) (opaqueE' p h0 h1 L S C) .a = 0 ∧
      bookGap (C ()) (opaqueDoCdt' p h0 h1 L S C) (opaqueE' p h0 h1 L S C) .a = 0) ∧
    ((C ()).w .b = 1 →
      bookGap (C ()) (opaqueR1State' p h0 h1 L S C) (opaqueE' p h0 h1 L S C) .b = 0 ∧
      bookGap (C ()) (opaqueDoCdt' p h0 h1 L S C) (opaqueE' p h0 h1 L S C) .b = 0) := by
  refine ⟨fun ha => ⟨?_, ?_⟩, fun hb => ⟨?_, ?_⟩⟩
  · exact opaque_gap'_r1 p h0 h1 L S C .a (by rw [ha]; norm_num)
  · rw [opaque_gap'_do_a p h0 h1 L S C (by rw [ha]; norm_num) hp hL, ha]; ring
  · exact opaque_gap'_r1 p h0 h1 L S C .b (by rw [hb]; norm_num)
  · have hs := (C ()).sum_one
    rw [Act2.sum_univ] at hs
    have ha : (C ()).w .a = 0 := by linarith
    rw [opaque_gap'_do_b p h0 h1 L S C (by rw [hb]; norm_num) hp hL, ha]; ring

/-- **T3, the inversion with the parameters free**: at a properly mixed label with `p ≥ ½`,
`L ≥ 0`, under Definition 6 the deviation referent (R1-state) is bitten at `qL(1−q)(2p−1)` and
the forcing referent (R3) spared (`Δ = 0`); under 6′ the deviation referent is spared and the
forcing (do-CDT) referent bitten at the same `qL(1−q)(2p−1)`. "The Dutch book condemns classical
CDT" is true in v2 only under the shared seed, and there against the do-construal.
Source: `repair/C2.md` C2-16′/C2-17′; `sl-defensible-claims.md` S12; P12-5/P12-15; mandate T3
(the Definition-6 inversion and its 6′ reversal)
Kind: L (the conjunction of the four proved gap theorems `opaque_gap_r1_a`, `opaque_gap_r3`,
`opaque_gap'_r1`, `opaque_gap'_do_a`, packaged; the content is theirs — audit round 1, N2)
Fidelity: exact for the Definition-6 half; variant for the 6′ half (do-construal, SE-1(d))
Hyps: (a) `0 < q < 1`, `½ ≤ p`, `0 ≤ L`; (c) the 6′ forcing value `opaqueDoCdt'` is SE-1(d)'s
do-construal (a defined-by-formula referent, not a run-law quantity of the shared seed) -/
theorem opaque_inversion (hqa : 0 < (C ()).w .a) (hqb : 0 < (C ()).w .b) (hp : 1 / 2 ≤ p)
    (hL : 0 ≤ L) :
    bookGap (C ()) (opaqueR1State p h0 h1 L S C) (opaqueE p h0 h1 L S C) .a =
        (C ()).w .a * L * (1 - (C ()).w .a) * (2 * p - 1) ∧
      bookGap (C ()) (opaqueR3 p h0 h1 L S C) (opaqueE p h0 h1 L S C) .a = 0 ∧
      bookGap (C ()) (opaqueR1State' p h0 h1 L S C) (opaqueE' p h0 h1 L S C) .a = 0 ∧
      bookGap (C ()) (opaqueDoCdt' p h0 h1 L S C) (opaqueE' p h0 h1 L S C) .a =
        (C ()).w .a * L * (1 - (C ()).w .a) * (2 * p - 1) :=
  ⟨opaque_gap_r1_a p h0 h1 L S C hqa hp hL, opaque_gap_r3 p h0 h1 L S C .a hqa,
    opaque_gap'_r1 p h0 h1 L S C .a hqa, opaque_gap'_do_a p h0 h1 L S C hqa hp hL⟩

/-- **The critic's two parametrizations under 6′**: `2q(1−q)` at `(¾, 4)` and `Lq(1−q)` at
`p = 1` — the same instances as `opaque_gap_r1_a_inst`, now for the do-CDT referent under the
shared seed; at `p = 1, L = 1` this is S12's `q(1−q)` (F-F).
Source: `sl-amendments.md` line 3 (critic C2); S12; mandate T3
Kind: N+
Fidelity: variant: 6′ do-construal
Hyps: (a) `0 < q`, `0 ≤ L` -/
theorem opaque_gap'_do_a_inst (hq : 0 < (C ()).w .a) (hL : 0 ≤ L) :
    bookGap (C ()) (opaqueDoCdt' (3/4) (by norm_num) (by norm_num) 4 S C)
        (opaqueE' (3/4) (by norm_num) (by norm_num) 4 S C) .a =
      2 * (C ()).w .a * (1 - (C ()).w .a) ∧
    bookGap (C ()) (opaqueDoCdt' 1 (by norm_num) (by norm_num) L S C)
        (opaqueE' 1 (by norm_num) (by norm_num) L S C) .a =
      L * (C ()).w .a * (1 - (C ()).w .a) := by
  refine ⟨?_, ?_⟩
  · rw [opaque_gap'_do_a (3/4) (by norm_num) (by norm_num) 4 S C hq (by norm_num) (by norm_num)]
    ring
  · rw [opaque_gap'_do_a 1 (by norm_num) (by norm_num) L S C hq (by norm_num) hL]
    ring

end opaqueSeed

end Cleanroom.Decision.DpDutchBook
