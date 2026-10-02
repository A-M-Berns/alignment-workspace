import Cleanroom.Corrigibility.LegitNegDynamic.Cells

/-!
# Conditioning across time: Dinkelbach's form of updateless and updateful P2 (D2(ii)/(iii))

Package `legit-neg-dynamic`, target 3 (load-bearing 1). Sources: `clusters/D/NEGATIVES.md` D2(ii),
D2(iii); `clusters/D/VERIFY.md` "D2 — narrowed" (V2: the positive-mass clause);
`clusters/D/fixtures/d2_conditioning_dynamic.py` (instances A, B; the Dinkelbach checks at
l. 76–84), `verify_D.py` V2; pinned by [[corr-legit-neg-inventory]] item 047.

The content is one lemma over an arbitrary finite `Problem`: with `λ*` **the maximum** of
`P1 / P(L | ·)` over the positive-mass options (a `sup'`, not a parameter — the mandate's trap),
`P1 a − λ* · P(L | a) ≤ 0` on positive-mass options with equality exactly at the P2-maximisers,
`P3` with every void world graded `λ*` equals `P1 − λ* P(L) + λ*`, and so
`argmaxOpt P2 = argmax (P3 (W ≡ λ*)) ∩ {P(L) > 0}` (`argmaxOpt_P2_eq_argmax_P3_inter`). Applied to
`P.restrict C` it is the **updateful** verdict at cell `C` with the cell's own `λ_C`; applied to the
policy problem of `Cells.lean` it is the **updateless** verdict, and the tower identity turns the
latter into "at every cell, P3 with `W ≡ λ*`" (`updateless_P2_iff_cellwise_P3`). The V2 witness
`v2` shows the intersection with `{P(L) > 0}` cannot be dropped: a surely-void option attains the
shifted maximum without being a P2 candidate (exclusion convention).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.LegitNegDynamic

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem
  Cleanroom.Corrigibility.LegitNegPricing

variable {S B : Type} [Fintype S] [Fintype B]

section General

variable [DecidableEq B]

variable (Q : Problem S B) (V : MenuVec S B)

open Classical in
/-- The options of positive legitimacy mass, `{a | 0 < P(L | a)}` — the domain on which P2 is
defined (exclusion convention).
Source: VERIFY D "D2 — narrowed" (V2)
Kind: D
Fidelity: exact -/
noncomputable def posMass : Finset B := univ.filter fun a => 0 < Q.PL a

/-- `mem_posMass`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_posMass {a : B} : a ∈ posMass Q ↔ 0 < Q.PL a := by simp [posMass]

/-- P2's value as a rational, `P1 V a / P(L | a)` (junk `… / 0` off `posMass`, where it is never
read: every use below is under `a ∈ posMass`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def ratio (a : B) : ℚ := Q.P1 V a / Q.PL a

/-- **`λ*`**: the maximum of P2's value over the positive-mass options (a `Finset.sup'`; it is a
maximum, not a parameter — the load-bearing point of D2(iii)).
Source: [[corr-legit-neg-inventory]] item 047 (D2(iii), "`λ* = max_π N/D`")
Kind: D
Fidelity: exact -/
noncomputable def lamStar (h : (posMass Q).Nonempty) : ℚ := (posMass Q).sup' h (ratio Q V)

/-- `ratio_le_lamStar`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ratio_le_lamStar (h : (posMass Q).Nonempty) {a : B} (ha : a ∈ posMass Q) :
    ratio Q V a ≤ lamStar Q V h :=
  Finset.le_sup' (ratio Q V) ha

/-- `λ*` is attained.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma exists_ratio_eq_lamStar (h : (posMass Q).Nonempty) :
    ∃ a ∈ posMass Q, ratio Q V a = lamStar Q V h := by
  obtain ⟨a, ha, hEq⟩ := Finset.exists_mem_eq_sup' h (ratio Q V)
  exact ⟨a, ha, hEq.symm⟩

/-- **Dinkelbach, the inequality**: `P1 a − λ* · P(L | a) ≤ 0` for every positive-mass option.
(`Finset.le_sup'` through `div_le_iff₀` — kind L; the Dinkelbach content of the row is
`argmaxOpt_P2_eq_argmax_P3_inter` and `mem_argmax_policyShifted_iff`.)
Source: [[corr-legit-neg-inventory]] item 047 (D2(iii)); VERIFY D V2 (the positive-mass clause)
Kind: L
Fidelity: exact
Hyps: (a) `a ∈ posMass` (V2's narrowing) -/
theorem P1_sub_lamStar_mul_PL_le (h : (posMass Q).Nonempty) {a : B} (ha : a ∈ posMass Q) :
    Q.P1 V a - lamStar Q V h * Q.PL a ≤ 0 := by
  have hpos := (mem_posMass Q).1 ha
  have hle := ratio_le_lamStar Q V h ha
  unfold ratio at hle
  rw [div_le_iff₀ hpos] at hle
  linarith

/-- **Dinkelbach, the equality case**: on a positive-mass option, `P1 a − λ* · P(L | a) = 0` iff
`a` attains `λ*`. (`div_eq_iff` — kind L.)
Source: [[corr-legit-neg-inventory]] item 047 (D2(iii))
Kind: L
Fidelity: exact
Hyps: (a) `a ∈ posMass` -/
theorem P1_sub_lamStar_mul_PL_eq_zero_iff (h : (posMass Q).Nonempty) {a : B}
    (ha : a ∈ posMass Q) :
    Q.P1 V a - lamStar Q V h * Q.PL a = 0 ↔ ratio Q V a = lamStar Q V h := by
  have hpos := (mem_posMass Q).1 ha
  unfold ratio
  rw [div_eq_iff hpos.ne']
  constructor <;> intro hx <;> linarith

/-- Attaining `λ*` is maximising P2's value over the positive-mass options.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ratio_eq_lamStar_iff (h : (posMass Q).Nonempty) {a : B} (ha : a ∈ posMass Q) :
    ratio Q V a = lamStar Q V h ↔ ∀ b ∈ posMass Q, ratio Q V b ≤ ratio Q V a := by
  constructor
  · intro heq b hb; rw [heq]; exact ratio_le_lamStar Q V h hb
  · intro hmax
    exact le_antisymm (ratio_le_lamStar Q V h ha) (Finset.sup'_le _ _ hmax)

/-- Off `posMass` the legitimacy mass is zero (it is never negative).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma PL_eq_zero_of_not_posMass {a : B} (ha : a ∉ posMass Q) : Q.PL a = 0 := by
  rw [mem_posMass, not_lt] at ha
  exact le_antisymm ha (Q.mass_nonneg _)

/-- **P3 with a constant void grade** `W ≡ lam`, `λ = 1`, is `P1 − lam · P(L | a) + lam`: the
shifted value, up to the constant `lam`.
Source: [[corr-legit-neg-inventory]] item 047 (D2(iii), "`𝔼[1_L V + 1_{¬L} λ*]`")
Kind: L
Fidelity: exact -/
theorem P3_const_one_eq (lam : ℚ) (a : B) :
    Q.P3 (fun _ _ _ => lam) 1 V a = Q.P1 V a - lam * Q.PL a + lam := by
  unfold Problem.P3 Problem.P1 Problem.PL Problem.mass
  have hterm : ∀ s, Q.prior s * (ind (Q.leg s a) * V s a a + ind (!Q.leg s a) * 1 * lam) =
      Q.prior s * ind (Q.leg s a) * V s a a - lam * (Q.prior s * ind (Q.leg s a)) + lam * Q.prior s := by
    intro s; rw [ind_not]; ring
  rw [Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Q.prior_sum, mul_one]

/-- The maximisers of the `λ*`-shifted value are exactly the options with `P1 − λ* P(L) = 0`
(the maximum of the shifted value is `0`: attained where `λ*` is attained, and every surely-void
option attains it too).
Source: [[corr-legit-neg-inventory]] item 047 (D2(iii)); VERIFY D V2
Kind: P
Fidelity: exact -/
theorem mem_argmax_P3_lamStar_iff (h : (posMass Q).Nonempty) (a : B) :
    a ∈ argmax (Q.P3 (fun _ _ _ => lamStar Q V h) 1 V) ↔
      Q.P1 V a - lamStar Q V h * Q.PL a = 0 := by
  have hle : ∀ b, Q.P1 V b - lamStar Q V h * Q.PL b ≤ 0 := by
    intro b
    by_cases hb : b ∈ posMass Q
    · exact P1_sub_lamStar_mul_PL_le Q V h hb
    · have h0 := PL_eq_zero_of_not_posMass Q hb
      rw [h0, Q.P1_eq_zero_of_PL_eq_zero V b h0]; simp
  obtain ⟨a₀, ha₀, heq⟩ := exists_ratio_eq_lamStar Q V h
  have h0 : Q.P1 V a₀ - lamStar Q V h * Q.PL a₀ = 0 :=
    (P1_sub_lamStar_mul_PL_eq_zero_iff Q V h ha₀).2 heq
  rw [mem_argmax]
  simp_rw [P3_const_one_eq]
  constructor
  · intro hmax; have := hmax a₀; linarith [hle a]
  · intro hz b; linarith [hle b]

/-- **D2(iii), narrowed as V2 requires (the load-bearing identity).** The P2-maximisers
(exclusion convention) are exactly the maximisers of P3 with every void world graded `λ*` **that
have positive legitimacy mass**:
`argmaxOpt (P2 V) = argmax (P3 (W ≡ λ*) 1 V) ∩ {a | 0 < P(L | a)}`.
Source: [[corr-legit-neg-inventory]] item 047 (D2(iii)); VERIFY D "D2 — narrowed" (V2)
Kind: P
Fidelity: exact (the narrowed claim; `v2_witness` shows the intersection is needed)
Hyps: (a) some option has positive mass -/
theorem argmaxOpt_P2_eq_argmax_P3_inter (h : (posMass Q).Nonempty) :
    argmaxOpt (Q.P2 V) = argmax (Q.P3 (fun _ _ _ => lamStar Q V h) 1 V) ∩ posMass Q := by
  ext a
  rw [Finset.mem_inter, mem_argmax_P3_lamStar_iff, mem_argmaxOpt]
  constructor
  · rintro ⟨x, hx, hmax⟩
    have hPL : Q.PL a ≠ 0 := by
      intro h0; rw [Q.P2_of_eq V a h0] at hx; cases hx
    have hpos : 0 < Q.PL a := lt_of_le_of_ne (Q.mass_nonneg _) (Ne.symm hPL)
    have ha : a ∈ posMass Q := (mem_posMass Q).2 hpos
    rw [Q.P2_of_ne V a hPL, Option.some_inj] at hx
    refine ⟨?_, ha⟩
    rw [P1_sub_lamStar_mul_PL_eq_zero_iff Q V h ha, ratio_eq_lamStar_iff Q V h ha]
    intro b hb
    have hb' := (mem_posMass Q).1 hb
    have := hmax b (ratio Q V b) (Q.P2_of_ne V b hb'.ne')
    unfold ratio; rw [hx]; exact this
  · rintro ⟨hz, ha⟩
    have hpos := (mem_posMass Q).1 ha
    refine ⟨ratio Q V a, Q.P2_of_ne V a hpos.ne', ?_⟩
    intro b y hy
    have hb : Q.PL b ≠ 0 := by
      intro h0; rw [Q.P2_of_eq V b h0] at hy; cases hy
    rw [Q.P2_of_ne V b hb, Option.some_inj] at hy
    rw [← hy]
    have hbm : b ∈ posMass Q := (mem_posMass Q).2 (lt_of_le_of_ne (Q.mass_nonneg _) (Ne.symm hb))
    exact ((ratio_eq_lamStar_iff Q V h ha).1
      ((P1_sub_lamStar_mul_PL_eq_zero_iff Q V h ha).1 hz)) b hbm

end General

/-! ### The updateful form: T2 at a cell with the cell's own `λ_C` -/

section T2

variable {A : Type} [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Updateful P2 at cell `C` is P3 with `W ≡ λ_C`**, `λ_C` the maximum of the T2 ratio over
the cell's positive-mass options (the instance of `argmaxOpt_P2_eq_argmax_P3_inter` at
`P.restrict C`).
Source: [[corr-legit-neg-inventory]] item 047 (D2(iii), "updateful conditioning at cell `I` is P3
with void worlds scored `λ_I`")
Kind: C
Fidelity: exact
Hyps: (a) positive cell mass; some option of positive mass within the cell -/
theorem T2_argmaxOpt_P2_eq (P : Problem S A) (V : MenuVec S A) (C : Finset S)
    (hC : 0 < ∑ t ∈ C, P.prior t) (h : (posMass (P.restrict C hC)).Nonempty) :
    argmaxOpt ((P.restrict C hC).P2 V) =
      argmax ((P.restrict C hC).P3 (fun _ _ _ => lamStar (P.restrict C hC) V h) 1 V)
        ∩ posMass (P.restrict C hC) :=
  argmaxOpt_P2_eq_argmax_P3_inter _ V h

end T2

/-! ### The updateless form: T1 over cell policies, and the cellwise identification -/

section T1

variable {A : Type} [Fintype A] [DecidableEq S] [DecidableEq A]
variable (P : Problem S A) (cellOf : S → Finset S) (V : MenuVec S A)

/-- The positive-mass cell policies `Λ = {π | 0 < policyPL π}` (as `posMass` of the policy
problem).
Source: VERIFY D V2
Kind: D
Fidelity: exact -/
noncomputable abbrev Lambda : Finset (CellPol (A := A) cellOf) := posMass (policyProblem P cellOf)

/-- `mem_Lambda`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_Lambda {π : CellPol (A := A) cellOf} : π ∈ Lambda P cellOf ↔ 0 < policyPL P π.1 :=
  mem_posMass _

/-- `Λ` is non-empty as soon as some action has positive legitimacy mass: its constant policy is a
positive-mass cell policy for every partition. (Discharges the `Nonempty` hypotheses of the
witnesses below and in `Partial.lean`.)
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Lambda_nonempty_of_PL_pos {a : A} (ha : 0 < P.PL a) : (Lambda P cellOf).Nonempty :=
  ⟨⟨fun _ => a, cellPolicy_const _ _⟩, by rw [mem_Lambda, policyPL_const]; exact ha⟩

/-- **`λ*` over policies**: the maximum of the T1 conditioning value over `Λ`.
Source: [[corr-legit-neg-inventory]] item 047 (D2(iii))
Kind: D
Fidelity: exact -/
noncomputable def lamStarT1 (h : (Lambda P cellOf).Nonempty) : ℚ :=
  lamStar (policyProblem P cellOf) (policyVec cellOf V) h

/-- The shifted policy value is `policyValue − lam · policyPL + lam`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyShifted_eq (lam : ℚ) (π : S → A) :
    policyShifted P V lam π = policyValue P V π - lam * policyPL P π + lam := by
  unfold policyShifted policyValue policyPL
  have hterm : ∀ s, P.prior s * (ind (P.leg s (π s)) * V s (π s) (π s) + ind (!P.leg s (π s)) * lam) =
      P.prior s * ind (P.leg s (π s)) * V s (π s) (π s) - lam * (P.prior s * ind (P.leg s (π s)))
        + lam * P.prior s := by
    intro s; rw [ind_not]; ring
  rw [Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, P.prior_sum, mul_one]

/-- **Dinkelbach over policies**: for a positive-mass cell policy,
`policyValue π − λ* · policyPL π ≤ 0`, with equality iff `π` maximises `policyP2` on `Λ`.
Source: [[corr-legit-neg-inventory]] item 047 (D2(iii)); VERIFY D V2
Kind: C
Fidelity: exact
Hyps: (a) `π ∈ Λ` -/
theorem T1_dinkelbach (h : (Lambda P cellOf).Nonempty) {π : CellPol (A := A) cellOf}
    (hπ : π ∈ Lambda P cellOf) :
    policyValue P V π.1 - lamStarT1 P cellOf V h * policyPL P π.1 ≤ 0 ∧
    (policyValue P V π.1 - lamStarT1 P cellOf V h * policyPL P π.1 = 0 ↔
      ∀ π' ∈ Lambda P cellOf, policyValue P V π'.1 / policyPL P π'.1 ≤
        policyValue P V π.1 / policyPL P π.1) :=
  ⟨P1_sub_lamStar_mul_PL_le (policyProblem P cellOf) (policyVec cellOf V) h hπ,
   (P1_sub_lamStar_mul_PL_eq_zero_iff (policyProblem P cellOf) (policyVec cellOf V) h hπ).trans
     (ratio_eq_lamStar_iff (policyProblem P cellOf) (policyVec cellOf V) h hπ)⟩

/-- **Updateless P2 = the `λ*`-shifted value on `Λ`** (V2's form):
`argmaxOpt policyP2 = argmax (policyShifted λ*) ∩ Λ` over the cell policies.
Source: [[corr-legit-neg-inventory]] item 047 (D2(iii)); VERIFY D "D2 — narrowed"
Kind: C
Fidelity: exact (narrowed to `Λ`); exclusion convention
Hyps: (a) `Λ` non-empty -/
theorem argmaxOpt_policyP2_eq (h : (Lambda P cellOf).Nonempty) :
    argmaxOpt (fun π : CellPol (A := A) cellOf => policyP2 P V π.1) =
      argmax (fun π : CellPol (A := A) cellOf => policyShifted P V (lamStarT1 P cellOf V h) π.1)
        ∩ Lambda P cellOf := by
  have key := argmaxOpt_P2_eq_argmax_P3_inter (policyProblem P cellOf) (policyVec cellOf V) h
  have e1 : argmaxOpt (fun π : CellPol (A := A) cellOf => policyP2 P V π.1) =
      argmaxOpt ((policyProblem P cellOf).P2 (policyVec cellOf V)) := rfl
  have e2 : argmax (fun π : CellPol (A := A) cellOf =>
        policyShifted P V (lamStarT1 P cellOf V h) π.1) =
      argmax ((policyProblem P cellOf).P3 (fun _ _ _ => lamStarT1 P cellOf V h) 1
        (policyVec cellOf V)) :=
    argmax_congr (fun π => (policyProblem_P3_const P cellOf V _ π).symm)
  rw [e1, e2]; exact key

/-- **Separability: a cell policy maximises the `lam`-shifted T1 value iff at every cell it
prescribes a maximiser of T2's P3 with `W ≡ lam`** (the tower identity plus its converse).
Source: [[corr-legit-neg-inventory]] item 047 (D2(iii), "the left side is separable over cells")
Kind: P
Fidelity: exact
Hyps: (a) partition axioms -/
theorem mem_argmax_policyShifted_iff {P : Problem S A} {cellOf : S → Finset S}
    (hP : IsPartition P cellOf) (V : MenuVec S A) (lam : ℚ) (π : CellPol (A := A) cellOf) :
    π ∈ argmax (fun π : CellPol (A := A) cellOf => policyShifted P V lam π.1) ↔
      ∀ s, π.1 s ∈ argmax ((P.restrict (cellOf s) (hP.pos s)).P3 (fun _ _ _ => lam) 1 V) := by
  set U : S → A → ℚ := fun s a => ind (P.leg s a) * V s a a + ind (!P.leg s a) * lam with hU
  have hcell : ∀ s a, (P.restrict (cellOf s) (hP.pos s)).P3 (fun _ _ _ => lam) 1 V a =
      cellEU P U (cellOf s) a := fun s a => restrict_P3_const_eq_cellEU P V lam _ _ a
  constructor
  · intro hmax s
    rw [mem_argmax]; intro a; rw [hcell, hcell]
    have hco : CellOptimal P U cellOf π.1 :=
      cellOptimal_of_T1_optimal hP U π.2 (fun π' hπ' => (mem_argmax.1 hmax) ⟨π', hπ'⟩)
    exact hco.2 s a
  · intro hs
    rw [mem_argmax]; intro π'
    have hco : CellOptimal P U cellOf π.1 :=
      ⟨π.2, fun s a => by have := mem_argmax.1 (hs s) a; rwa [hcell, hcell] at this⟩
    exact cellOptimal_T1_optimal hP U hco π'.2

/-- **D2(iii), the identification (load-bearing 1).** For a partition, a cell policy is an
updateless P2-optimum (exclusion convention) iff it has positive legitimacy mass **and** at every
cell it prescribes a maximiser of the T2 graded proposal P3 with every void world scored `λ*`:
updateless conditioning *is* the graded proposal with the endogenous void grade `λ*`, the best
achievable T1 conditional value; the updateful verdict at a cell uses the cell's own `λ_C`
(`T2_argmaxOpt_P2_eq`), and the two part exactly when `λ*` and `λ_C` part (`Partial.lean`).
Source: [[corr-legit-neg-inventory]] item 047 (D2(iii)); VERIFY D V2 (positive-mass clause)
Kind: C
Fidelity: exact (V2's narrowed statement); exclusion convention
Hyps: (a) partition axioms; `Λ` non-empty -/
theorem updateless_P2_iff_cellwise_P3 {P : Problem S A} {cellOf : S → Finset S}
    (hP : IsPartition P cellOf) (V : MenuVec S A) (h : (Lambda P cellOf).Nonempty)
    (π : CellPol (A := A) cellOf) :
    π ∈ argmaxOpt (fun π : CellPol (A := A) cellOf => policyP2 P V π.1) ↔
      0 < policyPL P π.1 ∧ ∀ s, π.1 s ∈ argmax ((P.restrict (cellOf s) (hP.pos s)).P3
        (fun _ _ _ => lamStarT1 P cellOf V h) 1 V) := by
  rw [argmaxOpt_policyP2_eq P cellOf V h, Finset.mem_inter, mem_Lambda,
    mem_argmax_policyShifted_iff hP V]
  exact and_comm

end T1

/-! ### V2: the positive-mass clause is needed -/

/-- **V2's problem**: one state, `x = 0` keeps legitimacy with `u = 1/2`, `y = 1` voids surely
(`verify_D.py` V2).
Source: VERIFY D V2
Kind: D
Fidelity: exact -/
def v2 : Problem (Fin 1) (Fin 2) where
  prior := ![1]
  prior_nonneg := by intro s; fin_cases s; simp
  prior_sum := by simp
  leg := fun _ a => decide (a = 0)
  u := fun _ a => if a = 0 then 1/2 else 0

/-- `v2_posMass`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma v2_posMass : posMass v2 = {0} := by
  ext a
  simp only [mem_posMass, Finset.mem_singleton]
  fin_cases a <;> simp [v2, Problem.PL, Problem.mass]

/-- `posMass v2` is inhabited (by `x`), so `v2_witness` assumes nothing.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma v2_posMass_nonempty : (posMass v2).Nonempty := by
  rw [v2_posMass]; exact Finset.singleton_nonempty 0

/-- **V2 witness (N+ for the positive-mass clause)**: `λ* = 1/2`; P2 picks `x` alone, while P3
with void worlds graded `λ*` ties `x` and `y` — the surely-void `y` attains the shifted maximum
without being a P2 candidate. Exclusion convention. (No hypothesis: the non-emptiness `lamStar`
needs is `v2_posMass_nonempty`.)
Source: VERIFY D "D2 — narrowed" (V2)
Kind: N+
Fidelity: exact -/
theorem v2_witness :
    lamStar v2 (S1 v2.u) v2_posMass_nonempty = 1/2 ∧ argmaxOpt (v2.P2 (S1 v2.u)) = {0} ∧
    argmax (v2.P3 (fun _ _ _ => (1/2 : ℚ)) 1 (S1 v2.u)) = univ := by
  have hPL0 : v2.PL 0 = 1 := by simp [v2, Problem.PL, Problem.mass]
  have hPL1 : v2.PL 1 = 0 := by simp [v2, Problem.PL, Problem.mass]
  have hP10 : v2.P1 (S1 v2.u) 0 = 1/2 := by simp [v2, Problem.P1, S1]
  have hP11 : v2.P1 (S1 v2.u) 1 = 0 := v2.P1_eq_zero_of_PL_eq_zero _ _ hPL1
  have hr0 : ratio v2 (S1 v2.u) 0 = 1/2 := by unfold ratio; rw [hP10, hPL0]; norm_num
  have h0mem : (0 : Fin 2) ∈ posMass v2 := (mem_posMass v2).2 (by rw [hPL0]; norm_num)
  have hl : lamStar v2 (S1 v2.u) v2_posMass_nonempty = 1/2 := by
    apply le_antisymm
    · have hall : ∀ a : Fin 2, 0 < v2.PL a → ratio v2 (S1 v2.u) a ≤ 1/2 := by
        rw [Fin.forall_fin_two]
        exact ⟨fun _ => hr0.le, fun ha => by rw [hPL1] at ha; exact absurd ha (lt_irrefl 0)⟩
      exact Finset.sup'_le _ _ fun a ha => hall a ((mem_posMass v2).1 ha)
    · rw [← hr0]; exact Finset.le_sup' (ratio v2 (S1 v2.u)) h0mem
  have h2_0 : v2.P2 (S1 v2.u) 0 = some (1/2) := by
    rw [v2.P2_of_ne _ _ (by rw [hPL0]; norm_num), hPL0, hP10]; norm_num
  have h2_1 : v2.P2 (S1 v2.u) 1 = none := v2.P2_of_eq _ _ hPL1
  refine ⟨hl, ?_, ?_⟩
  · refine finset_fin2_ext ?_ ?_
    · rw [mem_argmaxOpt, Finset.mem_singleton]
      refine ⟨fun _ => rfl, fun _ => ⟨1/2, h2_0, ?_⟩⟩
      rw [Fin.forall_fin_two]
      constructor
      · intro y hy; rw [h2_0, Option.some_inj] at hy; exact hy.symm.le
      · intro y hy; rw [h2_1] at hy; cases hy
    · rw [mem_argmaxOpt, Finset.mem_singleton]
      constructor
      · rintro ⟨x, hx, _⟩; rw [h2_1] at hx; cases hx
      · intro h10; exact absurd h10 (by decide)
  · rw [argmax_fin2_eq_univ_iff, P3_const_one_eq, P3_const_one_eq, hP10, hPL0, hPL1, hP11]
    norm_num

/-! ### D2(ii): the two instances, over the `Problem` of record -/

/-- The two-cell partition of `Fin 3`: cell `i₁ = {0, 1}`, cell `i₂ = {2}`.
Source: `d2_conditioning_dynamic.py:14-30`
Kind: D
Fidelity: exact -/
def d2cell : Fin 3 → Finset (Fin 3) := ![{0, 1}, {0, 1}, {2}]

/-- **Instance A** (`d2_conditioning_dynamic.py:40-53`): in `i₁`, `x = 0` keeps legitimacy with
`V = 1/2`, `y = 1` keeps it on state `0` only (mass `1/20` of `i₁`'s `1/2`) with `V = 9/10`; in
`i₂` (state `2`) both actions keep legitimacy and score `3/10` (the fixture's single action `z`).
Source: [[corr-legit-neg-inventory]] item 047 (D2(ii), instance A)
Kind: D
Fidelity: exact -/
def d2A : Problem (Fin 3) (Fin 2) where
  prior := ![1/20, 9/20, 1/2]
  prior_nonneg := by intro s; fin_cases s <;> simp <;> norm_num
  prior_sum := by simp [Fin.sum_univ_three]; norm_num
  leg := fun s a => !(decide (s = 1) && decide (a = 1))
  u := fun s a => if s = 2 then 3/10 else if a = 0 then 1/2 else if s = 0 then 9/10 else 0

/-- **Instance B** (`d2_conditioning_dynamic.py:56-68`): in `i₁`, `x` keeps with `V = 2/5`, `y`
keeps with probability `1/100` (state `0`, mass `1/200`) with `V = 1/10`; `i₂` scores `9/10`.
Source: [[corr-legit-neg-inventory]] item 047 (D2(ii), instance B)
Kind: D
Fidelity: exact -/
def d2B : Problem (Fin 3) (Fin 2) where
  prior := ![1/200, 99/200, 1/2]
  prior_nonneg := by intro s; fin_cases s <;> simp <;> norm_num
  prior_sum := by simp [Fin.sum_univ_three]; norm_num
  leg := fun s a => !(decide (s = 1) && decide (a = 1))
  u := fun s a => if s = 2 then 9/10 else if a = 0 then 2/5 else if s = 0 then 1/10 else 0

/-- `d2cell` is a partition of `d2A`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma d2A_partition : IsPartition d2A d2cell where
  mem := by decide
  cell := by decide
  pos := by intro s; fin_cases s <;> simp [d2cell, d2A] <;> norm_num

/-- `d2cell` is a partition of `d2B`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma d2B_partition : IsPartition d2B d2cell where
  mem := by decide
  cell := by decide
  pos := by intro s; fin_cases s <;> simp [d2cell, d2B] <;> norm_num

/-- On the two instances every cell policy has the T1 values of the constant policy of its
`i₁`-action (the two actions coincide on `i₂`), so the T1 verdict over cell policies is the T1
verdict over the menu.
Source: none: infrastructure (the fixture's single action `z` in `i₂`)
Kind: L
Fidelity: n/a -/
lemma d2_policy_values (P : Problem (Fin 3) (Fin 2)) (hleg : ∀ a, P.leg 2 a = true)
    (hu : ∀ a, P.u 2 a = P.u 2 0) (π : CellPol (A := Fin 2) d2cell) :
    policyValue P (S1 P.u) π.1 = P.P1 (S1 P.u) (π.1 0) ∧ policyPL P π.1 = P.PL (π.1 0) := by
  have h10 : π.1 1 = π.1 0 := π.2 0 1 (by decide)
  have hl2 := hleg (π.1 2)
  have hl0 := hleg (π.1 0)
  have hu2 := hu (π.1 2)
  have hu0 := hu (π.1 0)
  unfold policyValue policyPL Problem.P1 Problem.PL Problem.mass
  refine ⟨?_, ?_⟩ <;> simp only [Fin.sum_univ_three, h10, S1, hl2, hl0, hu2, hu0]

/-- **D2(ii), instance A, at T1**: `P2 x = some (2/5)`, `P2 y = some (39/110)`, so the updateless
P2 policy keeps `x`; cdot keeps `x` too. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 047 (D2(ii) A); `d2_conditioning_dynamic.py:44-47`
Kind: N+
Fidelity: exact -/
theorem d2A_T1 :
    d2A.P2 (S1 d2A.u) 0 = some (2/5) ∧ d2A.P2 (S1 d2A.u) 1 = some (39/110) ∧
    argmaxOpt (d2A.P2 (S1 d2A.u)) = {0} ∧ argmax (d2A.P1 (S1 d2A.u)) = {0} := by
  have hPL0 : d2A.PL 0 = 1 := by simp [d2A, Problem.PL, Problem.mass, Fin.sum_univ_three]; norm_num
  have hPL1 : d2A.PL 1 = 11/20 := by simp [d2A, Problem.PL, Problem.mass, Fin.sum_univ_three]; norm_num
  have hP10 : d2A.P1 (S1 d2A.u) 0 = 2/5 := by
    simp [d2A, Problem.P1, S1, Fin.sum_univ_three]; norm_num
  have hP11 : d2A.P1 (S1 d2A.u) 1 = 39/200 := by
    simp [d2A, Problem.P1, S1, Fin.sum_univ_three]; norm_num
  have h0 : d2A.P2 (S1 d2A.u) 0 = some (2/5) := by
    rw [d2A.P2_of_ne _ _ (by rw [hPL0]; norm_num), hPL0, hP10]; norm_num
  have h1 : d2A.P2 (S1 d2A.u) 1 = some (39/110) := by
    rw [d2A.P2_of_ne _ _ (by rw [hPL1]; norm_num), hPL1, hP11]; norm_num
  refine ⟨h0, h1, ?_, ?_⟩
  · rw [argmaxOpt_eq_argmax_of_forall_some (g := ![2/5, 39/110])
      (by rw [Fin.forall_fin_two]; exact ⟨by simp [h0], by simp [h1]⟩)]
    rw [argmax_fin2_eq_zero_iff]; norm_num
  · rw [argmax_fin2_eq_zero_iff, hP10, hP11]; norm_num

/-- **D2(ii), instance A, at T2 in `i₁`**: `P2 x = some (1/2)`, `P2 y = some (9/10)`: conditioning
manages the news inside the cell and takes `y`; cdot keeps `x`. So P2's T1 policy (`x`) is not
what its T2 self does (`y`): dynamic inconsistency with no predictor anywhere. Exclusion
convention.
Source: [[corr-legit-neg-inventory]] item 047 (D2(ii) A); `d2_conditioning_dynamic.py:44-47`
Kind: N+
Fidelity: exact -/
theorem d2A_T2 :
    (d2A.restrict {0, 1} (d2A_partition.pos 0)).P2 (S1 d2A.u) 0 = some (1/2) ∧
    (d2A.restrict {0, 1} (d2A_partition.pos 0)).P2 (S1 d2A.u) 1 = some (9/10) ∧
    argmaxOpt ((d2A.restrict {0, 1} (d2A_partition.pos 0)).P2 (S1 d2A.u)) = {1} ∧
    argmax ((d2A.restrict {0, 1} (d2A_partition.pos 0)).P1 (S1 d2A.u)) = {0} := by
  set Q := d2A.restrict {0, 1} (d2A_partition.pos 0) with hQ
  have hcp : ∀ t, Q.prior t = ![1/10, 9/10, 0] t := by
    intro t; fin_cases t <;> simp [hQ, d2A, Problem.cellprior] <;> norm_num
  have hPL0 : Q.PL 0 = 1 := by
    simp only [Problem.PL, Problem.mass, Fin.sum_univ_three, hcp]; simp [hQ, d2A]; try norm_num
  have hPL1 : Q.PL 1 = 1/10 := by
    simp only [Problem.PL, Problem.mass, Fin.sum_univ_three, hcp]; simp [hQ, d2A]; try norm_num
  have hP10 : Q.P1 (S1 d2A.u) 0 = 1/2 := by
    simp only [Problem.P1, Fin.sum_univ_three, hcp]; simp [hQ, d2A, S1]; try norm_num
  have hP11 : Q.P1 (S1 d2A.u) 1 = 9/100 := by
    simp only [Problem.P1, Fin.sum_univ_three, hcp]; simp [hQ, d2A, S1]; try norm_num
  have h0 : Q.P2 (S1 d2A.u) 0 = some (1/2) := by
    rw [Q.P2_of_ne _ _ (by rw [hPL0]; norm_num), hPL0, hP10]; norm_num
  have h1 : Q.P2 (S1 d2A.u) 1 = some (9/10) := by
    rw [Q.P2_of_ne _ _ (by rw [hPL1]; norm_num), hPL1, hP11]; norm_num
  refine ⟨h0, h1, ?_, ?_⟩
  · rw [argmaxOpt_eq_argmax_of_forall_some (g := ![1/2, 9/10])
      (by rw [Fin.forall_fin_two]; exact ⟨by simp [h0], by simp [h1]⟩)]
    rw [argmax_fin2_eq_one_iff]; norm_num
  · rw [argmax_fin2_eq_zero_iff, hP10, hP11]; norm_num

/-- **D2(ii), instance A: the value of information by P2's own T1 objective is `−1/22`.** The
policy that hands the choice to the T2 self (`y` on `i₁`) is worth `39/110` at T1, the T1 optimum
`2/5`: P2 would pay to stay ignorant. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 047 (D2(ii) A, "negative VOI"); `d2_conditioning_dynamic.py:48-51`
Kind: N+
Fidelity: exact -/
theorem d2A_VOI_P2 :
    policyP2 d2A (S1 d2A.u) (fun _ => 1) = some (39/110) ∧
    policyP2 d2A (S1 d2A.u) (fun _ => 0) = some (2/5) ∧ (39/110 : ℚ) - 2/5 = -1/22 := by
  refine ⟨d2A_T1.2.1, d2A_T1.1, by norm_num⟩

/-- **D2(ii), instance B, at T1**: `P2 x = some (13/20)`, `P2 y = some (901/1010)`: the updateless
P2 policy takes `y`, voiding legitimacy in `i₁` with probability `99/100` to raise the conditional
average; cdot keeps `x`. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 047 (D2(ii) B); `d2_conditioning_dynamic.py:56-63`
Kind: N+
Fidelity: exact -/
theorem d2B_T1 :
    d2B.P2 (S1 d2B.u) 0 = some (13/20) ∧ d2B.P2 (S1 d2B.u) 1 = some (901/1010) ∧
    argmaxOpt (d2B.P2 (S1 d2B.u)) = {1} ∧ argmax (d2B.P1 (S1 d2B.u)) = {0} ∧
    1 - d2B.PL 1 = 99/200 := by
  have hPL0 : d2B.PL 0 = 1 := by simp [d2B, Problem.PL, Problem.mass, Fin.sum_univ_three]; norm_num
  have hPL1 : d2B.PL 1 = 101/200 := by simp [d2B, Problem.PL, Problem.mass, Fin.sum_univ_three]; norm_num
  have hP10 : d2B.P1 (S1 d2B.u) 0 = 13/20 := by
    simp [d2B, Problem.P1, S1, Fin.sum_univ_three]; norm_num
  have hP11 : d2B.P1 (S1 d2B.u) 1 = 901/2000 := by
    simp [d2B, Problem.P1, S1, Fin.sum_univ_three]; norm_num
  have h0 : d2B.P2 (S1 d2B.u) 0 = some (13/20) := by
    rw [d2B.P2_of_ne _ _ (by rw [hPL0]; norm_num), hPL0, hP10]; norm_num
  have h1 : d2B.P2 (S1 d2B.u) 1 = some (901/1010) := by
    rw [d2B.P2_of_ne _ _ (by rw [hPL1]; norm_num), hPL1, hP11]; norm_num
  refine ⟨h0, h1, ?_, ?_, by rw [hPL1]; norm_num⟩
  · rw [argmaxOpt_eq_argmax_of_forall_some (g := ![13/20, 901/1010])
      (by rw [Fin.forall_fin_two]; exact ⟨by simp [h0], by simp [h1]⟩)]
    rw [argmax_fin2_eq_one_iff]; norm_num
  · rw [argmax_fin2_eq_zero_iff, hP10, hP11]; norm_num

/-- **D2(ii), instance B, at T2 in `i₁`**: `P2 x = some (2/5)`, `P2 y = some (1/10)`: the T2 self
keeps `x` where the updateless policy voids. The reverse inconsistency. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 047 (D2(ii) B); `d2_conditioning_dynamic.py:59-63`
Kind: N+
Fidelity: exact -/
theorem d2B_T2 :
    (d2B.restrict {0, 1} (d2B_partition.pos 0)).P2 (S1 d2B.u) 0 = some (2/5) ∧
    (d2B.restrict {0, 1} (d2B_partition.pos 0)).P2 (S1 d2B.u) 1 = some (1/10) ∧
    argmaxOpt ((d2B.restrict {0, 1} (d2B_partition.pos 0)).P2 (S1 d2B.u)) = {0} ∧
    argmax ((d2B.restrict {0, 1} (d2B_partition.pos 0)).P1 (S1 d2B.u)) = {0} := by
  set Q := d2B.restrict {0, 1} (d2B_partition.pos 0) with hQ
  have hcp : ∀ t, Q.prior t = ![1/100, 99/100, 0] t := by
    intro t; fin_cases t <;> simp [hQ, d2B, Problem.cellprior] <;> norm_num
  have hPL0 : Q.PL 0 = 1 := by
    simp only [Problem.PL, Problem.mass, Fin.sum_univ_three, hcp]; simp [hQ, d2B]; try norm_num
  have hPL1 : Q.PL 1 = 1/100 := by
    simp only [Problem.PL, Problem.mass, Fin.sum_univ_three, hcp]; simp [hQ, d2B]; try norm_num
  have hP10 : Q.P1 (S1 d2B.u) 0 = 2/5 := by
    simp only [Problem.P1, Fin.sum_univ_three, hcp]; simp [hQ, d2B, S1]; try norm_num
  have hP11 : Q.P1 (S1 d2B.u) 1 = 1/1000 := by
    simp only [Problem.P1, Fin.sum_univ_three, hcp]; simp [hQ, d2B, S1]; try norm_num
  have h0 : Q.P2 (S1 d2B.u) 0 = some (2/5) := by
    rw [Q.P2_of_ne _ _ (by rw [hPL0]; norm_num), hPL0, hP10]; norm_num
  have h1 : Q.P2 (S1 d2B.u) 1 = some (1/10) := by
    rw [Q.P2_of_ne _ _ (by rw [hPL1]; norm_num), hPL1, hP11]; norm_num
  refine ⟨h0, h1, ?_, ?_⟩
  · rw [argmaxOpt_eq_argmax_of_forall_some (g := ![2/5, 1/10])
      (by rw [Fin.forall_fin_two]; exact ⟨by simp [h0], by simp [h1]⟩)]
    rw [argmax_fin2_eq_zero_iff]; norm_num
  · rw [argmax_fin2_eq_zero_iff, hP10, hP11]; norm_num

/-! ### The `sup'`s of record on instance A: `λ* = 2/5`, `λ_C = 9/10`, and the headline end to end -/

/-- Instance A's T1 numbers: `PL x = 1`, `PL y = 11/20`, `P1 x = 2/5`, `P1 y = 39/200`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma d2A_values :
    d2A.PL 0 = 1 ∧ d2A.PL 1 = 11/20 ∧ d2A.P1 (S1 d2A.u) 0 = 2/5 ∧ d2A.P1 (S1 d2A.u) 1 = 39/200 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [d2A, Problem.PL, Problem.mass, Fin.sum_univ_three]; norm_num
  · simp [d2A, Problem.PL, Problem.mass, Fin.sum_univ_three]; norm_num
  · simp [d2A, Problem.P1, S1, Fin.sum_univ_three]; norm_num
  · simp [d2A, Problem.P1, S1, Fin.sum_univ_three]; norm_num

/-- Instance A's T2 numbers at `i₁ = {0, 1}`: `PL x = 1`, `PL y = 1/10`, `P1 x = 1/2`, `P1 y = 9/100`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma d2A_i1_values :
    (d2A.restrict {0, 1} (d2A_partition.pos 0)).PL 0 = 1 ∧
    (d2A.restrict {0, 1} (d2A_partition.pos 0)).PL 1 = 1/10 ∧
    (d2A.restrict {0, 1} (d2A_partition.pos 0)).P1 (S1 d2A.u) 0 = 1/2 ∧
    (d2A.restrict {0, 1} (d2A_partition.pos 0)).P1 (S1 d2A.u) 1 = 9/100 := by
  set Q := d2A.restrict {0, 1} (d2A_partition.pos 0) with hQ
  have hcp : ∀ t, Q.prior t = ![1/10, 9/10, 0] t := by
    intro t; fin_cases t <;> simp [hQ, d2A, Problem.cellprior] <;> norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Problem.PL, Problem.mass, Fin.sum_univ_three, hcp]; simp [hQ, d2A]; try norm_num
  · simp only [Problem.PL, Problem.mass, Fin.sum_univ_three, hcp]; simp [hQ, d2A]; try norm_num
  · simp only [Problem.P1, Fin.sum_univ_three, hcp]; simp [hQ, d2A, S1]; try norm_num
  · simp only [Problem.P1, Fin.sum_univ_three, hcp]; simp [hQ, d2A, S1]; try norm_num

/-- `Λ` on instance A with the two-cell partition is inhabited ("`x` everywhere" has mass `1`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma d2A_Lambda_nonempty : (Lambda d2A d2cell).Nonempty :=
  Lambda_nonempty_of_PL_pos d2A d2cell (a := 0) (by rw [d2A_values.1]; norm_num)

/-- **`λ* = 2/5` on instance A** — the `sup'` of record over `Λ` (not the fixture's numeral):
bounded on every positive-mass cell policy through `d2_policy_values` and attained by "`x`
everywhere".
Source: [[corr-legit-neg-inventory]] item 047 (D2(iii) fixture check); `d2_conditioning_dynamic.py:76-84`
Kind: P
Fidelity: exact -/
theorem d2A_lamStarT1 : lamStarT1 d2A d2cell (S1 d2A.u) d2A_Lambda_nonempty = 2/5 := by
  have hleg : ∀ a, d2A.leg 2 a = true := by intro a; simp [d2A]
  have hu : ∀ a, d2A.u 2 a = d2A.u 2 0 := by intro a; simp [d2A]
  obtain ⟨hPL0, hPL1, hP10, hP11⟩ := d2A_values
  have hbound : ∀ π ∈ Lambda d2A d2cell,
      ratio (policyProblem d2A d2cell) (policyVec d2cell (S1 d2A.u)) π ≤ 2/5 := by
    intro π hπ
    have hpos : 0 < policyPL d2A π.1 := (mem_Lambda _ _).1 hπ
    obtain ⟨hv, hp⟩ := d2_policy_values d2A hleg hu π
    unfold ratio
    rw [policyProblem_P1, policyProblem_PL, div_le_iff₀ hpos, hv, hp]
    generalize π.1 0 = a
    fin_cases a <;> simp [d2A, Problem.P1, Problem.PL, Problem.mass, S1, Fin.sum_univ_three] <;> norm_num
  have hx : ratio (policyProblem d2A d2cell) (policyVec d2cell (S1 d2A.u))
      ⟨fun _ => 0, cellPolicy_const _ _⟩ = 2/5 := by
    unfold ratio
    rw [policyProblem_P1, policyProblem_PL, policyValue_const, policyPL_const, hP10, hPL0]; norm_num
  have hxmem : (⟨fun _ => 0, cellPolicy_const _ _⟩ : CellPol (A := Fin 2) d2cell) ∈ Lambda d2A d2cell := by
    rw [mem_Lambda, policyPL_const, hPL0]; norm_num
  unfold lamStarT1 lamStar
  apply le_antisymm
  · exact Finset.sup'_le _ _ hbound
  · rw [← hx]; exact Finset.le_sup' _ hxmem

/-- Both actions have positive mass at `i₁` in instance A (nothing is excluded there).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma d2A_i1_posMass : posMass (d2A.restrict {0, 1} (d2A_partition.pos 0)) = univ := by
  obtain ⟨hPL0, hPL1, -, -⟩ := d2A_i1_values
  apply Finset.eq_univ_of_forall
  rw [Fin.forall_fin_two]
  exact ⟨by rw [mem_posMass, hPL0]; norm_num, by rw [mem_posMass, hPL1]; norm_num⟩

/-- `posMass` at `i₁` is inhabited.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma d2A_i1_posMass_nonempty : (posMass (d2A.restrict {0, 1} (d2A_partition.pos 0))).Nonempty := by
  rw [d2A_i1_posMass]; exact univ_nonempty

/-- **`λ_C = 9/10` at `i₁` on instance A** — the cell's `sup'` of record (`ratio x = 1/2`,
`ratio y = 9/10`).
Source: [[corr-legit-neg-inventory]] item 047 (D2(iii) fixture check); `d2_conditioning_dynamic.py:76-84`
Kind: P
Fidelity: exact -/
theorem d2A_lamC :
    lamStar (d2A.restrict {0, 1} (d2A_partition.pos 0)) (S1 d2A.u) d2A_i1_posMass_nonempty = 9/10 := by
  obtain ⟨hPL0, hPL1, hP10, hP11⟩ := d2A_i1_values
  have r0 : ratio (d2A.restrict {0, 1} (d2A_partition.pos 0)) (S1 d2A.u) 0 = 1/2 := by
    unfold ratio; rw [hP10, hPL0]; norm_num
  have r1 : ratio (d2A.restrict {0, 1} (d2A_partition.pos 0)) (S1 d2A.u) 1 = 9/10 := by
    unfold ratio; rw [hP11, hPL1]; norm_num
  have hall : ∀ a : Fin 2, ratio (d2A.restrict {0, 1} (d2A_partition.pos 0)) (S1 d2A.u) a ≤ 9/10 := by
    rw [Fin.forall_fin_two]; exact ⟨by rw [r0]; norm_num, by rw [r1]⟩
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun a _ => hall a
  · rw [← r1]; exact Finset.le_sup' _ (by rw [d2A_i1_posMass]; exact mem_univ 1)

/-- **The Dinkelbach check on instance A** (`d2_conditioning_dynamic.py:76-84`): the T1 P2 verdict
`{x}` is the verdict of the `λ*`-shifted value with `λ*` **the `sup'` of record** (`= 2/5`,
`d2A_lamStarT1`); the T2 verdict `{y}` in `i₁` is the verdict of the shifted value with the cell's
`λ_C`, again the `sup'` of record (`= 9/10`, `d2A_lamC`). Both sides computed from the definitions
of record; no numeral is plugged.
Source: [[corr-legit-neg-inventory]] item 047 (D2(iii) fixture check)
Kind: N+
Fidelity: exact -/
theorem d2A_dinkelbach_check :
    argmax (d2A.P3 (fun _ _ _ => lamStarT1 d2A d2cell (S1 d2A.u) d2A_Lambda_nonempty) 1 (S1 d2A.u)) = {0} ∧
    argmax ((d2A.restrict {0, 1} (d2A_partition.pos 0)).P3
      (fun _ _ _ => lamStar (d2A.restrict {0, 1} (d2A_partition.pos 0)) (S1 d2A.u) d2A_i1_posMass_nonempty)
      1 (S1 d2A.u)) = {1} := by
  rw [d2A_lamStarT1, d2A_lamC]
  obtain ⟨hPL0, hPL1, hP10, hP11⟩ := d2A_values
  obtain ⟨hQL0, hQL1, hQ10, hQ11⟩ := d2A_i1_values
  constructor
  · rw [argmax_fin2_eq_zero_iff, P3_const_one_eq, P3_const_one_eq, hPL0, hPL1, hP10, hP11]; norm_num
  · rw [argmax_fin2_eq_one_iff, P3_const_one_eq, P3_const_one_eq, hQL0, hQL1, hQ10, hQ11]; norm_num

/-- **The load-bearing identity on instance A, end to end**: "`x` everywhere" is an updateless
P2-optimum among the cell policies of the two-cell partition, derived through
`updateless_P2_iff_cellwise_P3` with the `sup'` of record (`λ* = 2/5`): positive mass, and at
every cell a maximiser of T2's P3 with `W ≡ λ*`. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 047 (D2(iii)); audit r1 adversarial 3.2
Kind: N+
Fidelity: exact -/
theorem d2A_updateless_x :
    (⟨fun _ => 0, cellPolicy_const _ _⟩ : CellPol (A := Fin 2) d2cell)
      ∈ argmaxOpt (fun π : CellPol (A := Fin 2) d2cell => policyP2 d2A (S1 d2A.u) π.1) := by
  rw [updateless_P2_iff_cellwise_P3 d2A_partition (S1 d2A.u) d2A_Lambda_nonempty, d2A_lamStarT1]
  refine ⟨?_, ?_⟩
  · show 0 < policyPL d2A (fun _ => 0)
    rw [policyPL_const, d2A_values.1]; norm_num
  · intro s
    rw [mem_argmax]
    intro b
    rw [P3_const_one_eq, P3_const_one_eq]
    simp only [Problem.P1, Problem.PL, Problem.mass, restrict_prior, restrict_leg, Problem.cellprior]
    fin_cases s <;> fin_cases b <;>
      simp [d2cell, d2A, S1, Fin.sum_univ_three] <;> norm_num

/-- **D2(i)'s hypothesis package on a non-trivial partition**: "`x` everywhere" is cell-optimal for
cdot on instance A over `d2cell = {{0, 1}, {2}}`, so `cellOptimal_T1_optimal`, `P1_le_policyValue`
and `VOI_nonneg` are exercised with a partition that is neither `{s}` nor `univ`.
Source: [[corr-legit-neg-inventory]] item 046 (D2(i) witness); audit r1 adversarial 3.4
Kind: N+
Fidelity: exact -/
theorem d2A_cellOptimal_x :
    CellOptimal d2A (fun s a => ind (d2A.leg s a) * S1 d2A.u s a a) d2cell (fun _ => 0) := by
  refine ⟨cellPolicy_const _ _, fun s a => ?_⟩
  unfold cellEU Problem.cellprior
  fin_cases s <;> fin_cases a <;>
    simp [d2cell, d2A, S1, Fin.sum_univ_three] <;> norm_num

end Cleanroom.Corrigibility.LegitNegDynamic
