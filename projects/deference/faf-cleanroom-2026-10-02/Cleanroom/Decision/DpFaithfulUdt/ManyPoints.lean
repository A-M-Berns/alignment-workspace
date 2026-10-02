import Cleanroom.Decision.DpFaithfulUdt.Cluster
import Cleanroom.Decision.DpFaithfulUdt.SelfConfirming
import Cleanroom.Decision.DpCalibration.Limit

/-!
# L23 at many points: coordination by a single-optimum belief (T13), correlated priors (T14)

T13 and T14 of [[dp-faithful-udt-mandate]] (`faithful.md` FA-13′, FA-14′(iii)–(iv), FA-15).

* **The three-point exact tie** (FA-13′, `seq3_tie_refutation`): on the three sequential binary
  points with the table `v(aab) = v(bba) = 0`, every other profile `1`, under the self-model
  `(a,a,a)^ε` (`dp-calibration`'s `tremble`) and `s°` masked-prior-calibrated to it, the
  disposition values at `d₁` and `d₂` tie exactly — `V_{s°}(pol = a) = V_{s°}(pol = b) =
  1 − t + t²`, `t = ε/2` — and `d₃` is strict for `a` (`1 − t²` vs `2t − t²`, `t < ½`); all values
  are **derived from the tree** through `polEv_V_eq_value`, not pasted. So `UDT_{s°,pol} =
  Unif × Unif × δ_a`, which supports `(b,b,a)` of payoff `0`: value `¾ < 1 = V(a,a,a)`. A
  self-model concentrated on a joint optimum does not suffice (reading W of XC-14 refuted); the
  struck sentence "every single deviation from `(a,a,a)` is optimal" is not restated (`v(aab) = 0`).
* **Two binary points coordinate** (FA-14′(iii), `seq2_tremble_inclusion`): for *every* rational
  table `v` on the two-point sequential binary tree and every optimal pure `π*`, there is an
  explicit `ε₀ > 0` such that for `0 < ε < ε₀` every profile of componentwise best replies to
  `(π*)^ε` is optimal — the order-`t` argument (`b ∈ BR₁` forces `v(b, π*₂) = M` and
  `v(b, b̄) ≥ v(π*₁, b̄)`; symmetrically; hence the off-profile is `≥ M`), not an enumeration.
  Hence `T_opt(UDT_{s°,pol})` (`seq2_tremble_udtProc_isOptimal`).
* **Correlated priors are not product self-models** (FA-15(a), `corrLaw_not_pi`): the law
  `½δ_{(a,a)} + ½δ_{(b,b)}` on the two-point tuples is not `⨂_d p_d` for any `p`
  (`w(a,a)·w(b,b) = ¼ ≠ 0 = w(a,b)·w(b,a)`), hence not the root law of any `lift U C'`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFaithfulUdt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt

/-- `|A| = 2` for the binary action type. Source: none: infrastructure. Kind: L -/
theorem Act2.card_eq : (Fintype.card Act2 : ℚ) = 2 := by
  have : Fintype.card Act2 = 2 := by decide
  rw [this]; norm_num

/-- The tremble of a deterministic procedure at a binary point: `1 − ε/2` on the prescribed act,
`ε/2` on the other (`t := ε/2` of the sources).
Source: [[decision-problems-v2]] Definition 10; `faithful.md` FA-13′ ("`t := ε/2`"); mandate
decision 6
Kind: L -/
theorem tremble_ofFun_w {ι : Type} [DecidableEq ι] (π : ι → Act2) (ε : ℚ) (h0 : 0 ≤ ε)
    (h1 : ε ≤ 1) (d : ι) (a : Act2) :
    (tremble (Proc.ofFun π : Proc ι (fun _ => Act2) ℚ) ε h0 h1 d).w a =
      if a = π d then 1 - ε / 2 else ε / 2 := by
  simp only [tremble, Proc.ofFun_w, Act2.card_eq]
  split_ifs <;> ring

/-- The other binary act. Source: none: infrastructure. Kind: D -/
def other : Act2 → Act2
  | .a => .b
  | .b => .a

/-- A binary act is the prescribed one or the other one. Source: none: infrastructure. Kind: L -/
theorem act2_eq_or_eq_other (x y : Act2) : x = y ∨ x = other y := by
  cases x <;> cases y <;> simp [other]

/-- `other y ≠ y`. Source: none: infrastructure. Kind: L -/
theorem other_ne (y : Act2) : other y ≠ y := by cases y <;> simp [other]

/-! ### Two sequential binary points with a general table -/

section seq2

/-- **The two-point sequential binary tree with payoff table `v`** (`d₁` then `d₂`, no chance, the
world records both acts). The Stag Hunt and FA-11's coordination miniature are instances.
Source: `faithful.md` §"Q10, many points" ("sequential `d₁ → d₂`, `O = ⊤`, acts recorded");
FA-14′(iii) ("two binary points")
Kind: D -/
def seq2 (v : Act2 → Act2 → ℚ) : Tree MiniW Pt2 (fun _ => Act2) ℚ :=
  .decision .p1 fun a => .decision .p2 fun b => .leaf (a, b) (v a b)

/-- FA-11's coordination miniature: payoff `1` iff the acts agree.
Source: `faithful.md` FA-11 ("coordination miniature (payoff `1` iff equal)")
Kind: D -/
def coordPay : Act2 → Act2 → ℚ := fun a b => if a = b then 1 else 0

/-- The value on `seq2 v`. Source: none: infrastructure. Kind: L -/
theorem seq2_value (v : Act2 → Act2 → ℚ) (C : Proc Pt2 (fun _ => Act2) ℚ) :
    value C (seq2 v) = ∑ a, (C .p1).w a * ∑ b, (C .p2).w b * v a b := by
  simp [seq2, DpFairnessReloc.value_decision, DpFairnessReloc.value_leaf]

/-- The two-point profile `(x, y)`. Source: none: infrastructure. Kind: D -/
def pt2Fun (x y : Act2) : Pt2 → Act2
  | .p1 => x
  | .p2 => y

/-- The value of a deterministic procedure on `seq2 v` is its table entry.
Source: none: infrastructure
Kind: L -/
theorem seq2_value_ofFun (v : Act2 → Act2 → ℚ) (π : Pt2 → Act2) :
    value (Proc.ofFun π) (seq2 v) = v (π .p1) (π .p2) := by
  rcases h1 : π .p1 with _ | _ <;> rcases h2 : π .p2 with _ | _ <;>
    simp [seq2_value, Proc.ofFun, Act2.sum_univ, h1, h2]

/-- `seq2 v` is almost fair. Source: none: infrastructure. Kind: L -/
theorem seq2_almostFair (v : Act2 → Act2 → ℚ) : AlmostFair (seq2 v) := by
  intro d ℓ
  rcases ℓ with ⟨a, b, ⟨⟩⟩
  cases d <;> simp [seq2]

/-- The deviation of the trembled `π` at `d₁` to `x` has value `(1 − t) v(x, π₂) + t v(x, π̄₂)`.
Source: `faithful.md` FA-14′(iii) (the order-`t` expansion)
Kind: L -/
theorem seq2_tremble_dev_p1 (v : Act2 → Act2 → ℚ) (π : Pt2 → Act2) (ε : ℚ) (h0 : 0 ≤ ε)
    (h1 : ε ≤ 1) (x : Act2) :
    value ((tremble (Proc.ofFun π) ε h0 h1).deviatePure .p1 x) (seq2 v) =
      (1 - ε / 2) * v x (π .p2) + ε / 2 * v x (other (π .p2)) := by
  rcases hp : π .p2 with _ | _ <;>
    simp [seq2_value, Proc.deviatePure, Proc.deviate, Function.update_apply, tremble_ofFun_w,
      Act2.sum_univ, hp, other, tremble, Proc.ofFun, Act2.card_eq] <;> ring

/-- The deviation of the trembled `π` at `d₂` to `y` has value `(1 − t) v(π₁, y) + t v(π̄₁, y)`.
Source: `faithful.md` FA-14′(iii)
Kind: L -/
theorem seq2_tremble_dev_p2 (v : Act2 → Act2 → ℚ) (π : Pt2 → Act2) (ε : ℚ) (h0 : 0 ≤ ε)
    (h1 : ε ≤ 1) (y : Act2) :
    value ((tremble (Proc.ofFun π) ε h0 h1).deviatePure .p2 y) (seq2 v) =
      (1 - ε / 2) * v (π .p1) y + ε / 2 * v (other (π .p1)) y := by
  rcases hp : π .p1 with _ | _ <;>
    simp [seq2_value, Proc.deviatePure, Proc.deviate, Function.update_apply, tremble_ofFun_w,
      Act2.sum_univ, hp, other, tremble, Proc.ofFun, Act2.card_eq] <;> ring

/-- The order-`t` lemma: if `(1 − t)·A ≤ t·D` with `A ≥ 0`, `0 < t` and `t` below `A/(A + |D| + 1)`
whenever `A > 0`, then `A = 0` and `D ≥ 0`.
Source: `faithful.md` FA-14′(iii) ("order-`t` argument")
Kind: L -/
theorem order_t_lemma (A D t : ℚ) (hA : 0 ≤ A) (ht : 0 < t)
    (hsmall : 0 < A → t < A / (A + |D| + 1)) (h : (1 - t) * A ≤ t * D) : A = 0 ∧ 0 ≤ D := by
  have hD : t * D ≤ t * |D| := mul_le_mul_of_nonneg_left (le_abs_self D) ht.le
  have hA0 : A = 0 := by
    by_contra hne
    have hpos : 0 < A := lt_of_le_of_ne hA (Ne.symm hne)
    have hb := hsmall hpos
    have hden : 0 < A + |D| + 1 := by positivity
    rw [lt_div_iff₀ hden] at hb
    nlinarith [abs_nonneg D]
  subst hA0
  refine ⟨rfl, ?_⟩
  by_contra hneg
  push_neg at hneg
  nlinarith

/-- The explicit tremble threshold for one point: `A/(A + |D| + 1)` when the gap `A` is positive,
`1` otherwise. Source: `faithful.md` FA-14′(iii) ("`ε` small"). Kind: D -/
def trembleBound (A D : ℚ) : ℚ := if 0 < A then A / (A + |D| + 1) else 1

/-- The threshold is positive. Source: none: infrastructure. Kind: L -/
theorem trembleBound_pos (A D : ℚ) : 0 < trembleBound A D := by
  unfold trembleBound
  split_ifs with h
  · exact div_pos h (by positivity)
  · exact one_pos

/-- Below the threshold the order-`t` lemma applies. Source: none: infrastructure. Kind: L -/
theorem trembleBound_spec (A D t : ℚ) (ht : t < trembleBound A D) (hA : 0 < A) :
    t < A / (A + |D| + 1) := by
  unfold trembleBound at ht
  rwa [if_pos hA] at ht

/-- **T13(iii) — FA-14′(iii): two binary points always coordinate.** For every rational table `v`
on the two-point sequential binary tree and every optimal pure profile `π*`, there is an explicit
`ε₀ > 0` (the minimum of the two points' thresholds, doubled) such that for every `0 < ε < ε₀`
every profile of componentwise best replies to the trembled self-model `(π*)^ε` is optimal:
`∏_d BR_d((π*)^ε) ⊆ Π*`. Proof: the order-`t` argument — `b ∈ BR₁` forces `v(b, π*₂) = M` and
`v(b, b̄) ≥ v(π*₁, b̄)`, symmetrically at `d₂`, hence every off-profile is `≥ M`.
Source: `faithful.md` FA-14′(iii) ("Two binary points, `C' = (π*)^ε` for *any* `π* ∈ Π*`: FA-10′'s
inclusion holds — order-`t` argument … and brute force over all 81 tables"); dp-cf-2-009, 108
Kind: P
Fidelity: stronger (every rational table, not the `{0,1,2}` grid; explicit `ε₀`, no limit)
Hyps: (a) `π*` is an optimal assignment on `seq2 v` -/
theorem seq2_tremble_inclusion (v : Act2 → Act2 → ℚ) (π : Pt2 → Act2)
    (hπ : PureOptimal (seq2 v) π) :
    ∃ ε₀ : ℚ, 0 < ε₀ ∧ ∀ ε (h0 : 0 < ε) (h1 : ε ≤ 1), ε < ε₀ →
      ∀ π' : Pt2 → Act2, (∀ d, π' d ∈ BR (tremble (Proc.ofFun π) ε h0.le h1) (seq2 v) d) →
        PureOptimal (seq2 v) π' := by
  set M := v (π .p1) (π .p2) with hM
  have hle : ∀ x y, v x y ≤ M := by
    intro x y
    have := hπ (pt2Fun x y)
    rw [seq2_value_ofFun, seq2_value_ofFun] at this
    simpa [pt2Fun] using this
  set A₁ := M - v (other (π .p1)) (π .p2) with hA₁
  set D₁ := v (other (π .p1)) (other (π .p2)) - v (π .p1) (other (π .p2)) with hD₁
  set A₂ := M - v (π .p1) (other (π .p2)) with hA₂
  set D₂ := v (other (π .p1)) (other (π .p2)) - v (other (π .p1)) (π .p2) with hD₂
  refine ⟨2 * min (trembleBound A₁ D₁) (trembleBound A₂ D₂), by
    have := trembleBound_pos A₁ D₁; have := trembleBound_pos A₂ D₂
    positivity, ?_⟩
  intro ε h0 h1 hε π' hπ'
  have ht1 : ε / 2 < trembleBound A₁ D₁ := by
    have := min_le_left (trembleBound A₁ D₁) (trembleBound A₂ D₂); linarith
  have ht2 : ε / 2 < trembleBound A₂ D₂ := by
    have := min_le_right (trembleBound A₁ D₁) (trembleBound A₂ D₂); linarith
  have hA₁0 : 0 ≤ A₁ := by rw [hA₁]; linarith [hle (other (π .p1)) (π .p2)]
  have hA₂0 : 0 ≤ A₂ := by rw [hA₂]; linarith [hle (π .p1) (other (π .p2))]
  -- the best-reply consequences at each point
  have key1 : π' .p1 = other (π .p1) → A₁ = 0 ∧ 0 ≤ D₁ := by
    intro hx
    have hbr := (mem_BR _ _ _ _).mp (hπ' .p1) (π .p1)
    rw [seq2_tremble_dev_p1, seq2_tremble_dev_p1, hx] at hbr
    refine order_t_lemma A₁ D₁ (ε / 2) hA₁0 (by linarith) (fun hA => trembleBound_spec _ _ _ ht1 hA) ?_
    rw [hA₁, hD₁, hM]; linarith
  have key2 : π' .p2 = other (π .p2) → A₂ = 0 ∧ 0 ≤ D₂ := by
    intro hy
    have hbr := (mem_BR _ _ _ _).mp (hπ' .p2) (π .p2)
    rw [seq2_tremble_dev_p2, seq2_tremble_dev_p2, hy] at hbr
    refine order_t_lemma A₂ D₂ (ε / 2) hA₂0 (by linarith) (fun hA => trembleBound_spec _ _ _ ht2 hA) ?_
    rw [hA₂, hD₂, hM]; linarith
  -- the four profiles
  intro π''
  rw [seq2_value_ofFun, seq2_value_ofFun]
  refine (hle _ _).trans ?_
  rcases act2_eq_or_eq_other (π' .p1) (π .p1) with hx | hx <;>
    rcases act2_eq_or_eq_other (π' .p2) (π .p2) with hy | hy
  · rw [hx, hy]
  · obtain ⟨hA, -⟩ := key2 hy
    rw [hx, hy]; rw [hA₂] at hA; linarith
  · obtain ⟨hA, -⟩ := key1 hx
    rw [hx, hy]; rw [hA₁] at hA; linarith
  · obtain ⟨hA, hD⟩ := key1 hx
    obtain ⟨hA', -⟩ := key2 hy
    rw [hx, hy]; rw [hA₁] at hA; rw [hD₁] at hD; rw [hA₂] at hA'; linarith

/-- **T13(iii), the procedure form**: under the trembled optimal self-model with `ε < ε₀` and `s°`
masked-prior-calibrated to it, `UDT_{s°,pol}` is optimal on `seq2 v` (through FA-10′).
Source: `faithful.md` FA-14′(iii); FA-10′
Kind: C
Fidelity: exact
Hyps: (a) `π*` optimal; (a) `MaskedPriorCalibrated (lift univ (π*)^ε) (Rel (seq2 v)) s°` -/
theorem seq2_tremble_udtProc_isOptimal (v : Act2 → Act2 → ℚ) (π : Pt2 → Act2)
    (hπ : PureOptimal (seq2 v) π) :
    ∃ ε₀ : ℚ, 0 < ε₀ ∧ ∀ ε (h0 : 0 < ε) (h1 : ε ≤ 1), ε < ε₀ →
      ∀ s₀ : State (RW MiniW (fun _ => Act2) Finset.univ) ℚ,
        MaskedPriorCalibrated (lift Finset.univ (tremble (Proc.ofFun π) ε h0.le h1))
          (relocRoot Finset.univ (seq2 v)) s₀ →
        IsOptimal (udtProc s₀ (polEv Finset.univ)) (seq2 v) := by
  obtain ⟨ε₀, hε₀, h⟩ := seq2_tremble_inclusion v π hπ
  refine ⟨ε₀, hε₀, fun ε h0 h1 hε s₀ hcal => ?_⟩
  rw [isOptimal_udtProc_iff_support_subset_optima Finset.univ (seq2 v) _ s₀ (seq2_almostFair v)
    (Finset.subset_univ _) hcal]
  exact h ε h0 h1 hε

end seq2

/-! ### Three sequential binary points: the exact tie -/

section seq3

/-- **Three sequential binary points with payoff table `v`** (`threeCoal`'s shape with the payoff
as a parameter: `seq3 coalPay = threeCoal`).
Source: `faithful.md` FA-13′ ("three-point exact tie"); mandate decision 7
Kind: D -/
def seq3 (v : Act2 → Act2 → Act2 → ℚ) : Tree (Act2 × Act2 × Act2) Pt3 (fun _ => Act2) ℚ :=
  .decision .d1 fun a₁ => .decision .d2 fun a₂ => .decision .d3 fun a₃ =>
    .leaf (a₁, a₂, a₃) (v a₁ a₂ a₃)

/-- `seq3 coalPay` is `dp-local-opt`'s `threeCoal`. Source: none: infrastructure. Kind: L -/
theorem seq3_coalPay : seq3 coalPay = threeCoal := rfl

/-- **FA-13′'s table**: `v(aab) = v(bba) = 0`, every other profile `1`.
Source: `faithful.md` FA-13′ ("Table `v(aaa)=v(baa)=v(aba)=v(bab)=v(abb)=v(bbb)=1`, `v(aab)=v(bba)=0`")
Kind: D -/
def tieTable : Act2 → Act2 → Act2 → ℚ
  | .a, .a, .b => 0
  | .b, .b, .a => 0
  | _, _, _ => 1

/-- The value on `seq3 v`. Source: none: infrastructure. Kind: L -/
theorem seq3_value (v : Act2 → Act2 → Act2 → ℚ) (C : Proc Pt3 (fun _ => Act2) ℚ) :
    value C (seq3 v) =
      ∑ a₁, (C .d1).w a₁ * ∑ a₂, (C .d2).w a₂ * ∑ a₃, (C .d3).w a₃ * v a₁ a₂ a₃ := by
  simp [seq3, DpFairnessReloc.value_decision, DpFairnessReloc.value_leaf]

/-- `seq3 v` is almost fair. Source: none: infrastructure. Kind: L -/
theorem seq3_almostFair (v : Act2 → Act2 → Act2 → ℚ) : AlmostFair (seq3 v) := by
  intro d ℓ
  rcases ℓ with ⟨a₁, a₂, a₃, ⟨⟩⟩
  cases d <;> simp [seq3]

/-- The output `Unif × Unif × δ_a` of FA-13′. Source: `faithful.md` FA-13′. Kind: D -/
def mixAAAt : Proc Pt3 (fun _ => Act2) ℚ
  | .d1 => FinDistr.uniform
  | .d2 => FinDistr.uniform
  | .d3 => FinDistr.pure .a

/-- The six deviation values of the trembled `(a,a,a)` on the tie table, as polynomials in `ε`
(`t = ε/2`): `1 − t + t²` at `d₁`, `d₂` (both acts), `1 − t²` vs `2t − t²` at `d₃`.
Source: `faithful.md` FA-13′ ("`V_{s°}(ρ_{d₁}(a)) = V_{s°}(ρ_{d₁}(b)) = 1 − t + t²` exactly …
`d₃`: `1−t²` vs `2t−t²`")
Kind: P -/
theorem seq3_tie_values (ε : ℚ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (value ((tremble (prof3 .a .a .a) ε h0 h1).deviatePure .d1 .a) (seq3 tieTable) =
        1 - ε / 2 + ε ^ 2 / 4 ∧
      value ((tremble (prof3 .a .a .a) ε h0 h1).deviatePure .d1 .b) (seq3 tieTable) =
        1 - ε / 2 + ε ^ 2 / 4) ∧
    (value ((tremble (prof3 .a .a .a) ε h0 h1).deviatePure .d2 .a) (seq3 tieTable) =
        1 - ε / 2 + ε ^ 2 / 4 ∧
      value ((tremble (prof3 .a .a .a) ε h0 h1).deviatePure .d2 .b) (seq3 tieTable) =
        1 - ε / 2 + ε ^ 2 / 4) ∧
    (value ((tremble (prof3 .a .a .a) ε h0 h1).deviatePure .d3 .a) (seq3 tieTable) =
        1 - ε ^ 2 / 4 ∧
      value ((tremble (prof3 .a .a .a) ε h0 h1).deviatePure .d3 .b) (seq3 tieTable) =
        ε - ε ^ 2 / 4) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp [seq3_value, Proc.deviatePure, Proc.deviate, Function.update_apply, prof3,
      tremble_ofFun_w, Act2.sum_univ, tieTable, tremble, Proc.ofFun, Act2.card_eq] <;> ring

/-- **T13(iv) — FA-13′, the three-point exact tie refutes "a single-optimum belief suffices"**: on
`seq3 tieTable` under the self-model `(a,a,a)^ε` (`0 < ε < 1`) and `s°` masked-prior-calibrated
to it, the disposition values at `d₁` and `d₂` tie exactly (`1 − ε/2 + ε²/4`), `d₃` is strict for
`a` (`1 − ε²/4` vs `ε − ε²/4`), so `UDT_{s°,pol} = Unif × Unif × δ_a`, of value `¾ < 1 = V(a,a,a)`,
not optimal — although the self-model is concentrated on the joint optimum `(a,a,a)`. Scope:
reading W of XC-14 (self-model = tremble of an optimal assignment); reading S is `Open.lean`'s.
Source: `faithful.md` FA-13′ ("Output `Unif × Unif × δ_a` supports `(b,b,a)` of payoff `0`: value
`¾ < 1`"), FA-14′(v); dp-cf-2-009, 108
Kind: N+ (refutation witness)
Fidelity: exact (values derived from the tree; the tie is exact, not a limit)
Hyps: (a) `0 < ε < 1`; (a) `MaskedPriorCalibrated (lift univ (a,a,a)^ε) (Rel (seq3 tieTable)) s°` -/
theorem seq3_tie_refutation (ε : ℚ) (h0 : 0 < ε) (h1 : ε < 1)
    (s₀ : State (RW (Act2 × Act2 × Act2) (fun _ => Act2) Finset.univ) ℚ)
    (hcal : MaskedPriorCalibrated (lift Finset.univ (tremble (prof3 .a .a .a) ε h0.le h1.le))
      (relocRoot Finset.univ (seq3 tieTable)) s₀) :
    (s₀.V (polEv Finset.univ .d1 .a) = 1 - ε / 2 + ε ^ 2 / 4 ∧
      s₀.V (polEv Finset.univ .d1 .b) = 1 - ε / 2 + ε ^ 2 / 4) ∧
    (s₀.V (polEv Finset.univ .d3 .a) = 1 - ε ^ 2 / 4 ∧
      s₀.V (polEv Finset.univ .d3 .b) = ε - ε ^ 2 / 4) ∧
    udtProc s₀ (polEv Finset.univ) = mixAAAt ∧
    value mixAAAt (seq3 tieTable) = 3 / 4 ∧ value (prof3 .a .a .a) (seq3 tieTable) = 1 ∧
    ¬ IsOptimal (udtProc s₀ (polEv Finset.univ)) (seq3 tieTable) := by
  have hB := seq3_almostFair tieTable
  have hfs := hcal.1
  have hmem : ∀ d : Pt3, d ∈ (Finset.univ : Finset Pt3) := fun d => Finset.mem_univ d
  have hV : ∀ d a, s₀.V (polEv Finset.univ d a) =
      value ((tremble (prof3 .a .a .a) ε h0.le h1.le).deviatePure d a) (seq3 tieTable) :=
    fun d a => polEv_V_eq_value _ _ _ s₀ hB hcal.2 (hmem d) a (hfs (.inl d) a)
  have hpr : ∀ d a, 0 < s₀.pr (polEv Finset.univ d a) := fun d a => by
    rw [polEv_pr _ _ _ s₀ hcal.2 (hmem d)]; exact hfs (.inl d) a
  obtain ⟨⟨v1a, v1b⟩, ⟨v2a, v2b⟩, ⟨v3a, v3b⟩⟩ := seq3_tie_values ε h0.le h1.le
  have hd1 : udtProc s₀ (polEv Finset.univ) .d1 = FinDistr.uniform := by
    rw [udtProc_eq_uniformArgmax s₀ (polEv Finset.univ) Pt3.d1 (hpr Pt3.d1)]
    apply uniformArgmax_eq_uniform
    intro a b; rw [hV, hV]; cases a <;> cases b <;> simp [v1a, v1b]
  have hd2 : udtProc s₀ (polEv Finset.univ) .d2 = FinDistr.uniform := by
    rw [udtProc_eq_uniformArgmax s₀ (polEv Finset.univ) Pt3.d2 (hpr Pt3.d2)]
    apply uniformArgmax_eq_uniform
    intro a b; rw [hV, hV]; cases a <;> cases b <;> simp [v2a, v2b]
  have hd3 : udtProc s₀ (polEv Finset.univ) .d3 = FinDistr.pure .a := by
    rw [udtProc_eq_uniformArgmax s₀ (polEv Finset.univ) Pt3.d3 (hpr Pt3.d3)]
    apply uniformArgmax_eq_pure
    apply argmaxFull_act2_eq_a
    rw [hV, hV, v3a, v3b]; linarith
  have hudt : udtProc s₀ (polEv Finset.univ) = mixAAAt := by
    funext d; cases d
    · exact hd1
    · exact hd2
    · exact hd3
  have hmix : value mixAAAt (seq3 tieTable) = 3 / 4 := by
    simp [seq3_value, mixAAAt, Act2.sum_univ, tieTable, Act2.card_eq]
    norm_num
  have hopt : value (prof3 .a .a .a) (seq3 tieTable) = 1 := by
    simp [seq3_value, prof3, Proc.ofFun, Act2.sum_univ, tieTable]
  refine ⟨⟨by rw [hV, v1a], by rw [hV, v1b]⟩, ⟨by rw [hV, v3a], by rw [hV, v3b]⟩, hudt, hmix, hopt,
    ?_⟩
  rw [hudt]
  intro h
  have := h (prof3 .a .a .a)
  rw [hmix, hopt] at this
  norm_num at this

end seq3

/-! ### FA-15: correlated priors are not product self-models -/

section corr

/-- The constant tuple on the two relocated points. Source: none: infrastructure. Kind: D -/
def constTuple (x : Act2) : (d : ↥(Finset.univ : Finset Pt2)) → Act2 := fun _ => x

/-- The mixed tuple `(x, y)` on the two relocated points. Source: none: infrastructure. Kind: D -/
def mixedTuple (x y : Act2) : (d : ↥(Finset.univ : Finset Pt2)) → Act2 :=
  fun d => match d.1 with | .p1 => x | .p2 => y

/-- **FA-15(a) — a correlated law on the joint dispositions is not a product**: any law with
`w(a,a) = w(b,b) = ½` and `w(a,b) = w(b,a) = 0` (the law `½δ_{(a,a)} + ½δ_{(b,b)}`) is not
`⨂_d p_d` for any family `p` — `w(a,a) w(b,b) = ¼` while a product has
`w(a,a) w(b,b) = w(a,b) w(b,a) = 0`. Hence it is the root law of no `lift U C'`: correlated priors
are not Definition-11 self-models on `B` (procedures draw independently across points).
Source: `faithful.md` FA-15 ("Correlated laws are not Definition-11 self-models on `B`
(procedures draw independently across points)"); dp-cf-2-010
Kind: P
Fidelity: exact
Hyps: (a) the four weights of the law -/
theorem corrLaw_not_pi (q : FinDistr ℚ ((d : ↥(Finset.univ : Finset Pt2)) → Act2))
    (haa : q.w (constTuple .a) = 1 / 2) (hbb : q.w (constTuple .b) = 1 / 2)
    (hab : q.w (mixedTuple .a .b) = 0) (hba : q.w (mixedTuple .b .a) = 0) :
    ¬ ∃ p : (d : ↥(Finset.univ : Finset Pt2)) → FinDistr ℚ Act2,
      FinDistr.pi (K := ℚ) (acts := fun _ : Pt2 => Act2) Finset.univ p = q := by
  rintro ⟨p, hp⟩
  have hw : ∀ σ, q.w σ = ∏ d : ↥(Finset.univ : Finset Pt2), (p d).w (σ d) := by
    intro σ; rw [← hp, FinDistr.pi_w]
  have hprod : ∀ σ : (d : ↥(Finset.univ : Finset Pt2)) → Act2,
      (∏ d : ↥(Finset.univ : Finset Pt2), (p d).w (σ d)) =
        (p ⟨.p1, Finset.mem_univ _⟩).w (σ ⟨.p1, Finset.mem_univ _⟩) *
          (p ⟨.p2, Finset.mem_univ _⟩).w (σ ⟨.p2, Finset.mem_univ _⟩) := by
    intro σ
    have huniv : (Finset.univ : Finset (↥(Finset.univ : Finset Pt2))) =
        {⟨.p1, Finset.mem_univ _⟩, ⟨.p2, Finset.mem_univ _⟩} := by
      ext ⟨d, _⟩; cases d <;> simp
    rw [huniv, Finset.prod_insert (by simp), Finset.prod_singleton]
  rw [hw, hprod] at haa hbb hab hba
  simp only [constTuple, mixedTuple] at haa hbb hab hba
  nlinarith [haa, hbb, hab, hba, (p ⟨.p1, Finset.mem_univ _⟩).nonneg .a,
    (p ⟨.p1, Finset.mem_univ _⟩).nonneg .b, (p ⟨.p2, Finset.mem_univ _⟩).nonneg .a,
    (p ⟨.p2, Finset.mem_univ _⟩).nonneg .b]

end corr

end Cleanroom.Decision.DpFaithfulUdt
