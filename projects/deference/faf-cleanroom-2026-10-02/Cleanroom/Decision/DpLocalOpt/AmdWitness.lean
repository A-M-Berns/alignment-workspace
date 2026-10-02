import Cleanroom.Decision.DpLocalOpt.ChainRule
import Cleanroom.Decision.DpLocalOpt.Ssa
import Cleanroom.Decision.DpLocalOpt.Trees

/-!
# `dp-local-opt`: the absent-minded-driver witnesses (T3(a), T3(c), T4's table, T6's N−, T8(a)(b))

One-point trees over `Act2` make every mixed action `(r, 1 − r)` and every procedure a `procQ`,
so the four predicates reduce to statements about the value polynomial and the two numbers
`Φ(a)`, `Φ(b)` (`coherentAt_procQ_iff`, `thm1At_procQ_iff`, …). Everything below is computed from
the trees: `Φ` through `siaSum`'s node equations, `V` through the closed forms of `Trees.lean`.

Numbers, with `q := C(d)(a)`:
* `amd` (`(0; 4, 1)`): `V = (1−q)(3q+1)`; `Φ(a) = 4(1−q)`, `Φ(b) = 2 + 2q`; `Φ(a) − Φ(b) = 2 − 6q`;
  Theorem 1 holds iff `q = 1/3`; pure Definition 22 holds iff `q ≤ 2/3`; mixed Definition 22 and
  optimality hold iff `q = 1/3`.
* Wei Dai's `(1; 0, 2)`, `x := C(d)(CONT) = 1 − q`: `V = 2x² − x + 1`; `Φ(EXIT) = 1`,
  `Φ(CONT) = 4x`; Theorem 1 holds iff `x ∈ {0, 1/4, 1}`; `V(1/4) = 7/8` is the global minimum.
* ZO-6's `(2; 1, 5)`: `δ_a` is Theorem-1-ratified (`2 > 1`) and not pure-coherent (`5 > 2`).
* The merged Stag Hunt, `q := C(d)(S)`: `V = 3q² − 2q + 1`; `Φ(S) = 4q`, `Φ(H) = 2(1−q)`; fixed
  points `{0, 1/3, 1}`; `V(1/3) = 2/3` is the global minimum; `δ_H` is Theorem-1-ratified and not
  coherent.
-/

namespace Cleanroom.Decision.DpLocalOpt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue

/-! ### One-point `Act2` trees -/

section onePoint

/-- Every mixed action on `Act2` is `(r, 1 − r)` with `r := m(a)`.
Source: none: infrastructure
Kind: L -/
theorem FinDistr.eq_act2 (m : FinDistr ℚ Act2) :
    m = FinDistr.act2 (m.w .a) (m.nonneg .a) (m.w_le_one .a) := by
  apply FinDistr.ext'
  intro x
  have h := m.sum_one
  rw [Act2.sum_univ] at h
  cases x
  · rfl
  · simp only [FinDistr.act2_b]; linarith

/-- Every one-point procedure on `Act2` is a `procQ`.
Source: none: infrastructure
Kind: L -/
theorem Proc.unit_eq_procQ (C : Proc Unit (fun _ => Act2) ℚ) :
    C = procQ ((C ()).w .a) ((C ()).nonneg .a) ((C ()).w_le_one .a) := by
  funext u; cases u; exact FinDistr.eq_act2 (C ())

/-- Deviating a `procQ` to `(r, 1 − r)` is `procQ r`.
Source: none: infrastructure
Kind: L -/
theorem procQ_deviate (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (r : ℚ) (r0 : 0 ≤ r) (r1 : r ≤ 1) :
    (procQ q h0 h1).deviate () (FinDistr.act2 r r0 r1) = procQ r r0 r1 := by
  funext u; cases u; simp [Proc.deviate, procQ]

/-- `δ_a = (1, 0)`. Source: none: infrastructure. Kind: L -/
theorem pure_a_eq_act2 : (FinDistr.pure Act2.a : FinDistr ℚ Act2) =
    FinDistr.act2 1 zero_le_one le_rfl := by
  apply FinDistr.ext'; intro x; cases x <;> simp

/-- `δ_b = (0, 1)`. Source: none: infrastructure. Kind: L -/
theorem pure_b_eq_act2 : (FinDistr.pure Act2.b : FinDistr ℚ Act2) =
    FinDistr.act2 0 le_rfl zero_le_one := by
  apply FinDistr.ext'; intro x; cases x <;> simp

variable {Ω : Type} (B : Tree Ω Unit (fun _ => Act2) ℚ) (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1)

/-- On a one-point `Act2` tree, mixed coherence of `procQ q` is `V(r) ≤ V(q)` for every
`r ∈ [0,1]`.
Source: none: infrastructure (A30 read on a one-point tree)
Kind: L -/
theorem coherentAt_procQ_iff :
    CoherentAt (procQ q h0 h1) B () ↔
      ∀ r (r0 : 0 ≤ r) (r1 : r ≤ 1), value (procQ r r0 r1) B ≤ value (procQ q h0 h1) B := by
  unfold CoherentAt
  constructor
  · intro h r r0 r1
    have := h (FinDistr.act2 r r0 r1)
    rwa [procQ_deviate] at this
  · intro h m
    rw [FinDistr.eq_act2 m, procQ_deviate]
    exact h _ _ _

/-- On a one-point `Act2` tree, pure coherence of `procQ q` is `V(1) ≤ V(q)` and `V(0) ≤ V(q)`.
Source: none: infrastructure (v2 line 279 read on a one-point tree)
Kind: L -/
theorem coherentPureAt_procQ_iff :
    CoherentPureAt (procQ q h0 h1) B () ↔
      value (procQ 1 zero_le_one le_rfl) B ≤ value (procQ q h0 h1) B ∧
        value (procQ 0 le_rfl zero_le_one) B ≤ value (procQ q h0 h1) B := by
  unfold CoherentPureAt Proc.deviatePure
  constructor
  · intro h
    have ha := h .a; have hb := h .b
    rw [pure_a_eq_act2, procQ_deviate] at ha
    rw [pure_b_eq_act2, procQ_deviate] at hb
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩ x
    cases x
    · rwa [pure_a_eq_act2, procQ_deviate]
    · rwa [pure_b_eq_act2, procQ_deviate]

/-- On a one-point `Act2` tree, optimality of `procQ q` is `V(r) ≤ V(q)` for every `r ∈ [0,1]`.
Source: none: infrastructure (Definition 21 read on a one-point tree)
Kind: L -/
theorem isOptimal_procQ_iff :
    IsOptimal (procQ q h0 h1) B ↔
      ∀ r (r0 : 0 ≤ r) (r1 : r ≤ 1), value (procQ r r0 r1) B ≤ value (procQ q h0 h1) B := by
  unfold IsOptimal
  constructor
  · intro h r r0 r1; exact h _
  · intro h C'
    rw [Proc.unit_eq_procQ C']
    exact h _ _ _

/-- On a one-point `Act2` tree, Theorem 1's condition for `procQ q` reads: if `q > 0` then
`Φ(b) ≤ Φ(a)`, and if `q < 1` then `Φ(a) ≤ Φ(b)`.
Source: none: infrastructure (Theorem 1 read on a one-point tree)
Kind: L -/
theorem thm1At_procQ_iff :
    Thm1At (procQ q h0 h1) B () ↔
      (0 < q → siaSum (procQ q h0 h1) B () .b ≤ siaSum (procQ q h0 h1) B () .a) ∧
        (0 < 1 - q → siaSum (procQ q h0 h1) B () .a ≤ siaSum (procQ q h0 h1) B () .b) := by
  unfold Thm1At
  constructor
  · intro h
    exact ⟨fun hq => h .a hq .b, fun hq => h .b hq .a⟩
  · rintro ⟨ha, hb⟩ x hx y
    cases x <;> cases y
    · exact le_rfl
    · exact ha hx
    · exact hb hx
    · exact le_rfl

end onePoint

/-! ### The AMD shape: `Φ` from the tree -/

section amdShape

variable (r₀ r₁ r₂ q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1)

/-- `Φ(a) = r₀ + (1 − q) r₁` on `amdShape r₀ r₁ r₂`: forcing `a` at the root (`R = 1`) pays `r₀`;
forcing it at the second node (`R = 1 − q`) pays `r₁`.
Source: `repair/spectrum.md` SP-14 (`R₂ = 1 − x`, `G₂ = (4, 1)` on `amd`)
Kind: P -/
theorem amdShape_siaSum_a :
    siaSum (procQ q h0 h1) (amdShape r₀ r₁ r₂) () .a = r₀ + (1 - q) * r₁ := by
  simp only [amdShape, siaSum_decision_self, siaSum_leaf, Act2.sum_univ, value_decision,
    value_leaf, procQ, FinDistr.act2_a, FinDistr.act2_b]
  ring

/-- `Φ(b) = (q r₁ + (1 − q) r₂) + (1 − q) r₂` on `amdShape r₀ r₁ r₂`: forcing `b` at the root
pays the second node's value; forcing it at the second node pays `r₂`.
Source: `repair/spectrum.md` SP-14 (`G_top(b) = 3x + 1` on `amd`)
Kind: P -/
theorem amdShape_siaSum_b :
    siaSum (procQ q h0 h1) (amdShape r₀ r₁ r₂) () .b = (q * r₁ + (1 - q) * r₂) + (1 - q) * r₂ := by
  simp only [amdShape, siaSum_decision_self, siaSum_leaf, Act2.sum_univ, value_decision,
    value_leaf, procQ, FinDistr.act2_a, FinDistr.act2_b]
  ring

end amdShape

/-! ### v2's AMD `(0; 4, 1)` -/

section amd

variable (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1)

/-- `Φ(a) = 4(1 − q)` on the AMD.
Source: `repair/spectrum.md` SP-14; mandate T4 ("`Φ(a) = 4(1−x)`")
Kind: N+ -/
theorem amd_siaSum_a : siaSum (procQ q h0 h1) amd () .a = 4 * (1 - q) := by
  rw [← amdShape_eq_amd, amdShape_siaSum_a]; ring

/-- `Φ(b) = 2 + 2q` on the AMD.
Source: `repair/spectrum.md` SP-14; mandate T4 ("`Φ(b) = 2x + 2`")
Kind: N+ -/
theorem amd_siaSum_b : siaSum (procQ q h0 h1) amd () .b = 2 + 2 * q := by
  rw [← amdShape_eq_amd, amdShape_siaSum_b]; ring

/-- **The T2 witness**: `Φ(a) − Φ(b) = 2 − 6q = d/dq (1 − q)(3q + 1)` on the AMD.
Source: `repair/spectrum.md` SP-14 ("`∑_q R_q (G_q(a) − G_q(b)) = 2 − 6x = V'(x)`")
Kind: N+ -/
theorem amd_siaSum_sub : siaSum (procQ q h0 h1) amd () .a - siaSum (procQ q h0 h1) amd () .b =
    2 - 6 * q := by
  rw [amd_siaSum_a, amd_siaSum_b]; ring

/-- **SP-14's table**: `(Φ(a), Φ(b)) = (4, 2), (8/3, 8/3), (2, 3), (0, 4)` at
`q = 0, 1/3, 1/2, 1`.
Source: `repair/spectrum.md` SP-14; mandate T4
Kind: N+ -/
theorem amd_sia_table :
    siaSum (procQ 0 le_rfl zero_le_one) amd () .a = 4 ∧
    siaSum (procQ 0 le_rfl zero_le_one) amd () .b = 2 ∧
    siaSum (procQ (1/3) (by norm_num) (by norm_num)) amd () .a = 8/3 ∧
    siaSum (procQ (1/3) (by norm_num) (by norm_num)) amd () .b = 8/3 ∧
    siaSum (procQ (1/2) (by norm_num) (by norm_num)) amd () .a = 2 ∧
    siaSum (procQ (1/2) (by norm_num) (by norm_num)) amd () .b = 3 ∧
    siaSum (procQ 1 zero_le_one le_rfl) amd () .a = 0 ∧
    siaSum (procQ 1 zero_le_one le_rfl) amd () .b = 4 := by
  simp only [amd_siaSum_a, amd_siaSum_b]; norm_num

/-- **Theorem 1 on the AMD holds exactly at `q = 1/3`**; in particular both pure procedures fail
it.
Source: `repair/spectrum.md` SP-14 ("the support condition holds only at `x = 1/3`");
dp-cf-122 ("both pure procedures fail"); mandate T4
Kind: P (an exact characterisation; regraded from N+ in repair round 1, docstring aligned in
round 2) -/
theorem amd_thm1At_iff : Thm1At (procQ q h0 h1) amd () ↔ q = 1/3 := by
  rw [thm1At_procQ_iff, amd_siaSum_a, amd_siaSum_b]
  constructor
  · rintro ⟨ha, hb⟩
    by_cases hq0 : q = 0
    · subst hq0; have := hb (by norm_num); norm_num at this
    by_cases hq1 : q = 1
    · subst hq1; have := ha (by norm_num); norm_num at this
    have h1' := ha (lt_of_le_of_ne h0 (Ne.symm hq0))
    have h2' := hb (by
      have : q < 1 := lt_of_le_of_ne h1 hq1
      linarith)
    linarith
  · rintro rfl; norm_num

/-- **Pure Definition 22 on the AMD holds exactly for `q ≤ 2/3`** (A31: "the pure restriction of
Definition 22 admits every `x ∈ [0, 2/3]`").
Source: A31; SP-14 ("pure Definition 22 is too weak (coherent at `x = 0, 1/2`)")
Kind: P (an exact characterisation; regraded from N+ in repair round 1, docstring aligned in
round 2) -/
theorem amd_coherentPureAt_iff : CoherentPureAt (procQ q h0 h1) amd () ↔ q ≤ 2/3 := by
  rw [coherentPureAt_procQ_iff, amd_value, amd_value, amd_value]
  constructor
  · rintro ⟨-, hb⟩; nlinarith
  · intro h
    constructor
    · nlinarith
    · nlinarith

/-- **Mixed Definition 22 on the AMD holds exactly at `q = 1/3`.**
Source: A30; CA-21′ ("at `q = 1/3` both True; at `q = 1` both False")
Kind: P (an exact characterisation; regraded from N+ in repair round 1, docstring aligned in
round 2) -/
theorem amd_coherentAt_iff : CoherentAt (procQ q h0 h1) amd () ↔ q = 1/3 := by
  rw [coherentAt_procQ_iff]
  constructor
  · intro h
    have := h (1/3) (by norm_num) (by norm_num)
    rw [amd_value, amd_value] at this
    nlinarith [sq_nonneg (q - 1/3)]
  · rintro rfl r r0 r1
    rw [amd_value, amd_value]
    nlinarith [sq_nonneg (r - 1/3)]

/-- **Optimality on the AMD holds exactly at `q = 1/3`** (Proposition 5(c)).
Source: [[decision-problems-v2]] Proposition 5(c) ("the best procedure is `C(d)(a) = 1/3`")
Kind: P (an exact characterisation; regraded from N+ in repair round 1, docstring aligned in
round 2) -/
theorem amd_isOptimal_iff : IsOptimal (procQ q h0 h1) amd ↔ q = 1/3 := by
  rw [isOptimal_procQ_iff]
  constructor
  · intro h
    have := h (1/3) (by norm_num) (by norm_num)
    rw [amd_value, amd_value] at this
    nlinarith [sq_nonneg (q - 1/3)]
  · rintro rfl r r0 r1
    rw [amd_value, amd_value]
    nlinarith [sq_nonneg (r - 1/3)]

/-- **T3(a): v2's pure Definition 22 is strictly weaker than the mixed form under
self-succession — refuted as a best-response condition.** On the AMD at `δ_b` (always continue):
`V = 1`, both pure deviations give `≤ 1` (`0` and `1`), and the mixed deviation `C[d ↦ 1/3]`
gives `4/3 > 1`. Quoted (v2 line 279): "`C` is *`B`-coherent* if `V_B(C[d ↦ a]) ≤ V_B(C)` for
every queried `d` and `a ∈ A_d` — no single decision, deviating unilaterally at *all* of its
occurrences, can improve the interaction. A procedure-level Nash condition". Reading: the
displayed condition (pure `a`) as the best-response ("Nash") condition the sentence names.
ATTRIBUTION-UNVETTED as to v2's intent; the reading is Claim 3.1's and A30's. Surviving
neighbour: `CoherentAt` (mixed), `amd_coherentAt_iff`.
Source: [[decision-problems-v2]] §8 Definition 22 (line 279) | [[fable-slop-notes]] Claim 3.1 |
A30 | CA-21′ | dp-core-064 | dp-cf-048
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem coherentPure_not_coherent_amd :
    CoherentPureAt (procQ 0 le_rfl zero_le_one) amd () ∧
    ¬ CoherentAt (procQ 0 le_rfl zero_le_one) amd () ∧
    value (procQ 0 le_rfl zero_le_one) amd = 1 ∧
    value ((procQ 0 le_rfl zero_le_one).deviate ()
      (FinDistr.act2 (1/3) (by norm_num) (by norm_num))) amd = 4/3 := by
  refine ⟨(amd_coherentPureAt_iff 0 _ _).mpr (by norm_num),
    fun h => by have := (amd_coherentAt_iff 0 _ _).mp h; norm_num at this, ?_, ?_⟩
  · rw [amd_value]; norm_num
  · rw [procQ_deviate, amd_value]; norm_num

/-- **T3(a) at `q = 1/2`** (Claim 3.1's instance): `V = 5/4`, pure-coherent, not mixed-coherent
(`C[d ↦ 1/3]` gives `4/3 > 5/4`), and not optimal.
Source: [[fable-slop-notes]] Claim 3.1 ("On the AMD at `x = 1/2`: `V = 5/4`; pure deviations
give `0` and `1`, both `≤ 5/4`, so `x = 1/2` is `B`-coherent; but the mixed deviation `m = 1/3`
gives `4/3 > 5/4`")
Kind: N+ -/
theorem amd_half_pure_not_mixed :
    value (procQ (1/2) (by norm_num) (by norm_num)) amd = 5/4 ∧
    CoherentPureAt (procQ (1/2) (by norm_num) (by norm_num)) amd () ∧
    ¬ CoherentAt (procQ (1/2) (by norm_num) (by norm_num)) amd () ∧
    ¬ IsOptimal (procQ (1/2) (by norm_num) (by norm_num)) amd := by
  refine ⟨by rw [amd_value]; norm_num, (amd_coherentPureAt_iff _ _ _).mpr (by norm_num),
    fun h => by have := (amd_coherentAt_iff _ _ _).mp h; norm_num at this,
    fun h => by have := (amd_isOptimal_iff _ _ _).mp h; norm_num at this⟩

/-- **T3(c), incomparability, second half**: on the AMD at `q = 1/2` pure Definition 22 holds
while Theorem 1's condition fails (`Φ(a) − Φ(b) = −1`).
Source: A31 ("on Proposition 5(c)'s tree at `q = 1/2` the pure Definition-22 condition holds
while Theorem 1's fails (`V'(1/2) = −1`)")
Kind: N+ -/
theorem amd_half_coherentPure_not_thm1 :
    CoherentPureAt (procQ (1/2) (by norm_num) (by norm_num)) amd () ∧
    ¬ Thm1At (procQ (1/2) (by norm_num) (by norm_num)) amd () ∧
    siaSum (procQ (1/2) (by norm_num) (by norm_num)) amd () .a -
      siaSum (procQ (1/2) (by norm_num) (by norm_num)) amd () .b = -1 := by
  refine ⟨(amd_coherentPureAt_iff _ _ _).mpr (by norm_num),
    fun h => by have := (amd_thm1At_iff _ _ _).mp h; norm_num at this, ?_⟩
  rw [amd_siaSum_sub]; norm_num

/-- **At the AMD optimum `q = 1/3` all three conditions hold** (v2 comment (ii): "at the AMD
optimum `x = 1/3` both hold, as they must"), and Theorem 1's condition is *sufficient* there
(T16(i)).
Source: [[decision-problems-v2]] §8 comment (ii); `amd_at_third`; mandate T3(c), T16(i)
Kind: N+ -/
theorem amd_third_all :
    Thm1At (procQ (1/3) (by norm_num) (by norm_num)) amd () ∧
    CoherentAt (procQ (1/3) (by norm_num) (by norm_num)) amd () ∧
    CoherentPureAt (procQ (1/3) (by norm_num) (by norm_num)) amd () ∧
    IsOptimal (procQ (1/3) (by norm_num) (by norm_num)) amd :=
  ⟨(amd_thm1At_iff _ _ _).mpr rfl, (amd_coherentAt_iff _ _ _).mpr rfl,
    (amd_coherentPureAt_iff _ _ _).mpr (by norm_num), (amd_isOptimal_iff _ _ _).mpr rfl⟩

/-- **T16(i): on the AMD Theorem 1's condition is sufficient** — `Thm1At ↔ IsOptimal` for every
`procQ q`.
Source: mandate T16(i) ("on `amd`, `Thm1At ↔ x = 1/3 ↔ IsOptimal`")
Kind: C -/
theorem amd_thm1At_iff_isOptimal : Thm1At (procQ q h0 h1) amd () ↔ IsOptimal (procQ q h0 h1) amd := by
  rw [amd_thm1At_iff, amd_isOptimal_iff]

/-- **T6's N− for Theorem 2's support clause with a mixed optimum (A28(b))**: at the AMD optimum
`q = 1/3` both actions are in the support, yet `V_B(C[d ↦ a]) = 0 < 1 = V_B(C[d ↦ b])` — the
support of a mixed optimum need not lie in `argmax_a V_B(C[d ↦ a])`, which is why v2 states the
clause for deterministic `C` (`ssaValue_pure_le_of_isOptimal`).
Source: A28(b) ("Proposition 5(c) at `x = 1/3` has `V_B(C[d↦a]) = 0 < 1 = V_B(C[d↦b])`")
Kind: N−
Fidelity: variant: the clause's failure for a mixed optimum (v2 states it for deterministic `C`) -/
theorem amd_third_support_clause_fails :
    IsOptimal (procQ (1/3) (by norm_num) (by norm_num)) amd ∧
    0 < (procQ (1/3) (by norm_num) (by norm_num) ()).w .a ∧
    0 < (procQ (1/3) (by norm_num) (by norm_num) ()).w .b ∧
    value ((procQ (1/3) (by norm_num) (by norm_num)).deviatePure () .a) amd = 0 ∧
    value ((procQ (1/3) (by norm_num) (by norm_num)).deviatePure () .b) amd = 1 := by
  refine ⟨(amd_isOptimal_iff _ _ _).mpr rfl, by norm_num [procQ], by norm_num [procQ], ?_, ?_⟩
  · rw [Proc.deviatePure, pure_a_eq_act2, procQ_deviate, amd_value]; norm_num
  · rw [Proc.deviatePure, pure_b_eq_act2, procQ_deviate, amd_value]; norm_num

end amd

/-! ### ZO-6's AMD `(2; 1, 5)` -/

section zo6

/-- `V = 5 − 7q + 4q²` on `(2; 1, 5)`: convex, so the maximum over `[0,1]` is at a vertex
(`q = 0`, `V = 5`) — a nested tree with a deterministic optimum (T5(d)).
Source: mandate T5(d)
Kind: N+ -/
theorem zo6Amd_isOptimal_zero : IsOptimal (procQ 0 le_rfl zero_le_one) zo6Amd := by
  rw [isOptimal_procQ_iff]
  intro r r0 r1
  rw [zo6Amd_value, zo6Amd_value]
  nlinarith

/-- **T3(c), incomparability, first half**: on `(2; 1, 5)`, `δ_a` satisfies Theorem 1's
condition (`Φ(a) = 2 > 1 = Φ(b)`) and is not pure-coherent (`V(C[d ↦ b]) = 5 > 2 = V`).
Source: A31 ("the pure procedure `δ_a` satisfies Theorem 1's condition (`2 > 1`) while the
all-instance deviation to `b` yields `5 > 2`"); ZO-6
Kind: N+ -/
theorem zo6Amd_thm1_not_coherentPure :
    Thm1At (procQ 1 zero_le_one le_rfl) zo6Amd () ∧
    ¬ CoherentPureAt (procQ 1 zero_le_one le_rfl) zo6Amd () ∧
    siaSum (procQ 1 zero_le_one le_rfl) zo6Amd () .a = 2 ∧
    siaSum (procQ 1 zero_le_one le_rfl) zo6Amd () .b = 1 ∧
    value (procQ 1 zero_le_one le_rfl) zo6Amd = 2 ∧
    value (procQ 0 le_rfl zero_le_one) zo6Amd = 5 := by
  have ha : siaSum (procQ 1 zero_le_one le_rfl) zo6Amd () .a = 2 := by
    rw [zo6Amd, amdShape_siaSum_a]; norm_num
  have hb : siaSum (procQ 1 zero_le_one le_rfl) zo6Amd () .b = 1 := by
    rw [zo6Amd, amdShape_siaSum_b]; norm_num
  refine ⟨?_, ?_, ha, hb, by rw [zo6Amd_value]; norm_num, by rw [zo6Amd_value]; norm_num⟩
  · rw [thm1At_procQ_iff, ha, hb]
    exact ⟨fun _ => by norm_num, fun h => absurd h (by norm_num)⟩
  · rw [coherentPureAt_procQ_iff]
    simp only [zo6Amd_value]
    norm_num

end zo6

/-! ### Wei Dai's AMD `(1; 0, 2)` -/

section weiDai

variable (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1)

/-- `Φ(EXIT) = 1` on Wei Dai's AMD (P10's `sumEXIT`), now derived from the tree.
Source: `repair/P10.md` I1; `notes/lean/P10-weidai-amd.lean` (`sumEXIT(x) = 1·1 + x·0 = 1`)
Kind: N+ -/
theorem weiDai_siaSum_exit : siaSum (procQ q h0 h1) weiDai () .a = 1 := by
  rw [weiDai, amdShape_siaSum_a]; ring

/-- `Φ(CONT) = 4x`, `x := C(d)(CONT) = 1 − q` (P10's `sumCONT`), derived from the tree.
Source: `notes/lean/P10-weidai-amd.lean` (`sumCONT(x) = 1·((1−x)·0 + x·2) + x·2 = 4x`)
Kind: N+ -/
theorem weiDai_siaSum_cont : siaSum (procQ q h0 h1) weiDai () .b = 4 * (1 - q) := by
  rw [weiDai, amdShape_siaSum_b]; ring

/-- **Theorem 1 on Wei Dai's AMD holds exactly at `x ∈ {0, 1/4, 1}`** (`q = 1 − x`).
Source: `repair/P10.md` I1 ("the condition's fixed points are `x ∈ {0, 1/4, 1}`");
`P10-weidai-amd.lean` `thm1_interior_fixed_point`
Kind: N+ -/
theorem weiDai_thm1_iff : Thm1At (procQ q h0 h1) weiDai () ↔ q = 1 ∨ q = 3/4 ∨ q = 0 := by
  rw [thm1At_procQ_iff, weiDai_siaSum_exit, weiDai_siaSum_cont]
  constructor
  · rintro ⟨ha, hb⟩
    by_cases hq1 : q = 1
    · exact Or.inl hq1
    by_cases hq0 : q = 0
    · exact Or.inr (Or.inr hq0)
    have h1' := ha (lt_of_le_of_ne h0 (Ne.symm hq0))
    have h2' := hb (by have : q < 1 := lt_of_le_of_ne h1 hq1; linarith)
    right; left; linarith
  · rintro (rfl | rfl | rfl) <;> norm_num

/-- **Theorem 1 can select the global minimum**: on Wei Dai's AMD the interior fixed point
`x = 1/4` (`q = 3/4`) has `V = 7/8 ≤ V(q)` for every `q ∈ [0,1]`.
Source: `repair/P10.md` I1 ("the interior one being the global *minimum* of `V`: a first-order
condition can pick a minimum"); `P10-weidai-amd.lean` `quarter_is_global_min`, `V_quarter`;
dp-sl-036, dp-sl-2-070
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem weiDai_quarter_min :
    Thm1At (procQ (3/4) (by norm_num) (by norm_num)) weiDai () ∧
    value (procQ (3/4) (by norm_num) (by norm_num)) weiDai = 7/8 ∧
    ∀ r (r0 : 0 ≤ r) (r1 : r ≤ 1), 7/8 ≤ value (procQ r r0 r1) weiDai := by
  refine ⟨(weiDai_thm1_iff _ _ _).mpr (Or.inr (Or.inl rfl)), by rw [weiDai_value]; norm_num, ?_⟩
  intro r r0 r1
  rw [weiDai_value]
  nlinarith [sq_nonneg (r - 3/4)]

/-- **`δ_EXIT` is Theorem-1-ratified and not coherent** on Wei Dai's AMD: `V(δ_EXIT) = 1`, the
all-instance deviation to CONT gives `2`.
Source: `repair/P10.md` I1 ("the deterministic EXIT policy … satisfies the condition, while the
all-instance deviation to CONT is worth `2 > 1`"); `P10-weidai-amd.lean` `def22_fails_at_exit`
Kind: N+ -/
theorem weiDai_exit_thm1_not_coherentPure :
    Thm1At (procQ 1 zero_le_one le_rfl) weiDai () ∧
    ¬ CoherentPureAt (procQ 1 zero_le_one le_rfl) weiDai () ∧
    value (procQ 1 zero_le_one le_rfl) weiDai = 1 ∧
    value (procQ 0 le_rfl zero_le_one) weiDai = 2 := by
  refine ⟨(weiDai_thm1_iff _ _ _).mpr (Or.inl rfl), ?_, by rw [weiDai_value]; norm_num,
    by rw [weiDai_value]; norm_num⟩
  rw [coherentPureAt_procQ_iff]
  simp only [weiDai_value]
  norm_num

/-- **Wei Dai's AMD at `q = 0` (`δ_CONT`) is a mixed-coherent, Theorem-1-ratified profile with a
strict preference inside its support**: it is the one-point optimum (`V(r) = 2(1−r)² − (1−r) + 1
≤ 2 = V(0)`), and `Φ(EXIT) = 1 < 4 = Φ(CONT)` with support `{CONT}`. The nested strict-preference
inhabitant of `thm1At_of_coherentAt`'s hypothesis that the ledger's T3(b) row cites (audit r2
adversarial N3 / fidelity non-blocking 1: the `Φ` values were in the package, the coherence was
not).
Source: `sl-workflow/notes/repair/P10.md` I1; mandate T3(b), T8(a); audit r2 adversarial N3
(probe `weiDai_cont_coherent_strict`, adopted)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem weiDai_cont_coherent_strict :
    CoherentAt (procQ 0 le_rfl zero_le_one) weiDai () ∧
    Thm1At (procQ 0 le_rfl zero_le_one) weiDai () ∧
    siaSum (procQ 0 le_rfl zero_le_one) weiDai () .a = 1 ∧
    siaSum (procQ 0 le_rfl zero_le_one) weiDai () .b = 4 ∧
    value (procQ 0 le_rfl zero_le_one) weiDai = 2 := by
  refine ⟨?_, (weiDai_thm1_iff _ _ _).mpr (Or.inr (Or.inr rfl)), weiDai_siaSum_exit _ _ _, ?_,
    by rw [weiDai_value]; norm_num⟩
  · rw [coherentAt_procQ_iff]
    intro r r0 r1
    rw [weiDai_value, weiDai_value]
    nlinarith
  · rw [weiDai_siaSum_cont]; norm_num

end weiDai

/-! ### The merged Stag Hunt -/

section mergedStag

variable (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1)

/-- `Φ(S) = 4q` on the merged Stag Hunt.
Source: `repair/P10.md` P10-3′(i) ("Theorem-1 sums `S ↦ 4q`")
Kind: N+ -/
theorem mergedStag_siaSum_S : siaSum (procQ q h0 h1) mergedStag () .a = 4 * q := by
  simp only [mergedStag, siaSum_decision_self, siaSum_leaf, Act2.sum_univ, value_decision,
    value_leaf, procQ, FinDistr.act2_a, FinDistr.act2_b]
  ring

/-- `Φ(H) = 2(1 − q)` on the merged Stag Hunt.
Source: `repair/P10.md` P10-3′(i) ("`H ↦ 2(1−q)`")
Kind: N+ -/
theorem mergedStag_siaSum_H : siaSum (procQ q h0 h1) mergedStag () .b = 2 * (1 - q) := by
  simp only [mergedStag, siaSum_decision_self, siaSum_leaf, Act2.sum_univ, value_decision,
    value_leaf, procQ, FinDistr.act2_a, FinDistr.act2_b]
  ring

/-- **Theorem 1 on the merged Stag Hunt holds exactly at `q ∈ {0, 1/3, 1}`.**
Source: `repair/P10.md` P10-3′(i) ("fixed points `{0, 1/3, 1}`")
Kind: N+ -/
theorem mergedStag_thm1_iff : Thm1At (procQ q h0 h1) mergedStag () ↔ q = 1 ∨ q = 1/3 ∨ q = 0 := by
  rw [thm1At_procQ_iff, mergedStag_siaSum_S, mergedStag_siaSum_H]
  constructor
  · rintro ⟨ha, hb⟩
    by_cases hq1 : q = 1
    · exact Or.inl hq1
    by_cases hq0 : q = 0
    · exact Or.inr (Or.inr hq0)
    have h1' := ha (lt_of_le_of_ne h0 (Ne.symm hq0))
    have h2' := hb (by have : q < 1 := lt_of_le_of_ne h1 hq1; linarith)
    right; left; linarith
  · rintro (rfl | rfl | rfl) <;> norm_num

/-- **The merged Stag Hunt's interior fixed point `q = 1/3` is the global minimum** `V = 2/3`.
Source: `repair/P10.md` P10-3′(i) ("The tie `q = 1/3` is the global minimum of `V` (`2/3`)");
mandate T8(b)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem mergedStag_third_min :
    Thm1At (procQ (1/3) (by norm_num) (by norm_num)) mergedStag () ∧
    value (procQ (1/3) (by norm_num) (by norm_num)) mergedStag = 2/3 ∧
    ∀ r (r0 : 0 ≤ r) (r1 : r ≤ 1), 2/3 ≤ value (procQ r r0 r1) mergedStag := by
  refine ⟨(mergedStag_thm1_iff _ _ _).mpr (Or.inr (Or.inl rfl)),
    by rw [mergedStag_value]; norm_num, ?_⟩
  intro r r0 r1
  rw [mergedStag_value]
  nlinarith [sq_nonneg (r - 1/3)]

/-- **`δ_H` is Theorem-1-ratified and not coherent (pure or mixed) on the merged Stag Hunt**:
`Φ(S) = 0 < 2 = Φ(H)`, and the all-instance deviation to `S` gives `2 > 1`. "CDT+SIA cannot
coordinate same-point instances, EDT+SSA can."
Source: `repair/P10.md` P10-3′(i) ("At always-`H` Theorem 1 holds (`0 < 2`) while Definition 22
fails pure and mixed"); dp-sl-2-030
Kind: N+ -/
theorem mergedStag_H_thm1_not_coherent :
    Thm1At (procQ 0 le_rfl zero_le_one) mergedStag () ∧
    ¬ CoherentPureAt (procQ 0 le_rfl zero_le_one) mergedStag () ∧
    ¬ CoherentAt (procQ 0 le_rfl zero_le_one) mergedStag () ∧
    value (procQ 0 le_rfl zero_le_one) mergedStag = 1 ∧
    value (procQ 1 zero_le_one le_rfl) mergedStag = 2 := by
  have hpure : ¬ CoherentPureAt (procQ 0 le_rfl zero_le_one) mergedStag () := by
    rw [coherentPureAt_procQ_iff]
    simp only [mergedStag_value]
    norm_num
  refine ⟨(mergedStag_thm1_iff _ _ _).mpr (Or.inr (Or.inr rfl)), hpure,
    fun h => hpure (CoherentAt.pure _ _ h), by rw [mergedStag_value]; norm_num,
    by rw [mergedStag_value]; norm_num⟩

/-- **The merged Stag Hunt at `q = 1` (`δ_S`) is a mixed-coherent, Theorem-1-ratified profile
with a strict preference inside its support**: the one-point optimum (`V(r) = 3r² − 2r + 1 ≤ 2 =
V(1)`), with `Φ(H) = 0 < 4 = Φ(S)` and support `{S}`. The second nested strict-preference
inhabitant of `thm1At_of_coherentAt`'s hypothesis cited by the ledger's T3(b) row.
Source: `sl-workflow/notes/repair/P10.md` 3′(i); mandate T3(b), T8(b); audit r2 adversarial N3
(probe `mergedStag_S_coherent_strict`, adopted)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem mergedStag_S_coherent_strict :
    CoherentAt (procQ 1 zero_le_one le_rfl) mergedStag () ∧
    Thm1At (procQ 1 zero_le_one le_rfl) mergedStag () ∧
    siaSum (procQ 1 zero_le_one le_rfl) mergedStag () .a = 4 ∧
    siaSum (procQ 1 zero_le_one le_rfl) mergedStag () .b = 0 ∧
    value (procQ 1 zero_le_one le_rfl) mergedStag = 2 := by
  refine ⟨?_, (mergedStag_thm1_iff _ _ _).mpr (Or.inl rfl), ?_, ?_,
    by rw [mergedStag_value]; norm_num⟩
  · rw [coherentAt_procQ_iff]
    intro r r0 r1
    rw [mergedStag_value, mergedStag_value]
    nlinarith
  · rw [mergedStag_siaSum_S]; norm_num
  · rw [mergedStag_siaSum_H]; norm_num

end mergedStag

end Cleanroom.Decision.DpLocalOpt
