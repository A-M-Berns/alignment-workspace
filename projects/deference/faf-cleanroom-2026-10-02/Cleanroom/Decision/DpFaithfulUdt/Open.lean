import Cleanroom.Decision.DpFaithfulUdt.KfoldAffine
import Cleanroom.Decision.DpFaithfulUdt.ManyPoints

/-!
# Q10's remaining conjectures, stated (T18; T13(i)–(ii) general)

Every declaration here is **OPEN**: a precise statement with `sorry`, listed in
`run/wp/dp-faithful-udt/dp-faithful-udt-open.txt` with its reason. The proved instances stand
beside each one.

* **T18(a) — faithful `ρ` on nested fibers iff affine coupling, normalized** (`faithful.md`
  Open 1): over the `k`-fold mugging with a *normalized* coupling `b` (`b_0 = 0`, `b_k = 1`), a
  leaf-set law-faithful for *both* acts exists for every full-support self-model iff `b` is affine
  in the number of paying draws on `0..k`. Round 0 stated this without the normalization; round 1
  refuted that statement in both directions at `k = 2` (`KfoldAffine.lean`:
  `kfold_faithful_iff_affine_refuted`). The normalized `k = 2` case is proved
  (`kfold2_norm_faithful_both_iff_affine`), with the sharper per-act loci
  (`kfold2_norm_pay_faithful_iff`: `b_1 ∈ {½, 1}`; `kfold2_norm_refuse_faithful_iff`:
  `b_1 ∈ {0, ½}`); the per-act loci for general `k` are a second OPEN row
  (`kfold_pay_faithful_iff_locus_open`).
* **T18(b) — reading S for `n ≤ 4`** (`faithful.md` FA-13′ scope, Open 3): on three and four
  sequential binary points with a rational table, if every single deviation from an optimal
  `π*` is optimal, then for small `ε` every profile of best replies to `(π*)^ε` is optimal. The
  brute force over `{0,1}` tables finds no failure; the five-point witness (UNREVIEWED) shows
  it fails at `n = 5`. The two-point case is proved without the reading-S hypothesis
  (`seq2_tremble_inclusion`).
* **T13(i)–(ii), general — a strict best reply to itself coordinates** (`faithful.md` FA-14′(i)–(ii)):
  on an almost-fair tree, if `π*` is a strict best reply to itself at every queried point, then
  for small `ε` the best replies to `(π*)^ε` are `{π*_d}` at every point, so `UDT_{s°,pol} = π*`.
  The two-point instance is proved (`seq2_strict_bestReply`, with the explicit threshold); the
  general route is the product-mixture expansion (`value_eq_product_mixture`) with Bernoulli's
  inequality for the weight of `π*[d ↦ a]` and a bound `2M|Q|ε` on the rest.
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

/-! ### T13(ii) on two points, proved -/

section strict

/-- **T13(ii) on two binary points — a strict best reply to itself coordinates**: if `π*` is
optimal and strictly beats both single deviations, then for every `0 < ε < ε₀` (explicit) the
best replies to `(π*)^ε` are `{π*_d}` at both points; hence `UDT_{s°,pol} = π*` under a masked
prior calibrated to `(π*)^ε`.
Source: `faithful.md` FA-14′(ii) ("it suffices that `π* ∈ Π*` be a strict best reply to itself and
`C' = (π*)^ε`")
Kind: P
Fidelity: exact (two points; explicit threshold)
Hyps: (a) `π*` optimal and strict against both single deviations -/
theorem seq2_strict_bestReply (v : Act2 → Act2 → ℚ) (π : Pt2 → Act2)
    (hπ : PureOptimal (seq2 v) π)
    (hs1 : v (other (π .p1)) (π .p2) < v (π .p1) (π .p2))
    (hs2 : v (π .p1) (other (π .p2)) < v (π .p1) (π .p2)) :
    ∃ ε₀ : ℚ, 0 < ε₀ ∧ ∀ ε (h0 : 0 < ε) (h1 : ε ≤ 1), ε < ε₀ →
      ∀ d, BR (tremble (Proc.ofFun π) ε h0.le h1) (seq2 v) d = {π d} := by
  set M := v (π .p1) (π .p2) with hM
  set A₁ := M - v (other (π .p1)) (π .p2) with hA₁
  set D₁ := v (other (π .p1)) (other (π .p2)) - v (π .p1) (other (π .p2)) with hD₁
  set A₂ := M - v (π .p1) (other (π .p2)) with hA₂
  set D₂ := v (other (π .p1)) (other (π .p2)) - v (other (π .p1)) (π .p2) with hD₂
  have hA₁0 : 0 < A₁ := by rw [hA₁]; linarith
  have hA₂0 : 0 < A₂ := by rw [hA₂]; linarith
  refine ⟨2 * min (trembleBound A₁ D₁) (trembleBound A₂ D₂), by
    have := trembleBound_pos A₁ D₁; have := trembleBound_pos A₂ D₂
    positivity, ?_⟩
  intro ε h0 h1 hε d
  have ht1 : ε / 2 < trembleBound A₁ D₁ := by
    have := min_le_left (trembleBound A₁ D₁) (trembleBound A₂ D₂); linarith
  have ht2 : ε / 2 < trembleBound A₂ D₂ := by
    have := min_le_right (trembleBound A₁ D₁) (trembleBound A₂ D₂); linarith
  -- the other act is not a best reply, so the best-reply set is `{π d}`
  have hnot : other (π d) ∉ BR (tremble (Proc.ofFun π) ε h0.le h1) (seq2 v) d := by
    intro hmem
    have hbr := (mem_BR _ _ _ _).mp hmem (π d)
    cases d
    · rw [seq2_tremble_dev_p1, seq2_tremble_dev_p1] at hbr
      have := order_t_lemma A₁ D₁ (ε / 2) hA₁0.le (by linarith)
        (fun hA => trembleBound_spec _ _ _ ht1 hA) (by rw [hA₁, hD₁, hM]; linarith)
      linarith [this.1]
    · rw [seq2_tremble_dev_p2, seq2_tremble_dev_p2] at hbr
      have := order_t_lemma A₂ D₂ (ε / 2) hA₂0.le (by linarith)
        (fun hA => trembleBound_spec _ _ _ ht2 hA) (by rw [hA₂, hD₂, hM]; linarith)
      linarith [this.1]
  ext x
  rw [Finset.mem_singleton]
  constructor
  · intro hx
    rcases act2_eq_or_eq_other x (π d) with h | h
    · exact h
    · exact absurd (h ▸ hx) hnot
  · rintro rfl
    rw [mem_BR]
    intro b
    rcases act2_eq_or_eq_other b (π d) with h | h
    · rw [h]
    · by_contra hlt
      push_neg at hlt
      apply hnot
      rw [mem_BR]
      intro c
      rcases act2_eq_or_eq_other c (π d) with hc | hc
      · rw [hc, ← h]; exact hlt.le
      · rw [hc, ← h]

end strict

/-! ### The open statements -/

section open_

/-- **OPEN — T18(a), normalized: faithful `ρ` on nested fibers iff affine coupling.** On the
`k`-fold mugging (`k ≥ 2`, `x, y > 0`) with a *normalized* coupling `b` (`b_0 = 0`, `b_k = 1`: no
transfer under unanimous refusal, transfer under unanimous payment), a leaf-set law-faithful
(algebra `σ(coin, r)`) for both acts exists for every full-support self-model iff `b` is affine
on `0..k` (equivalently `b_j = j/k`). **Without the normalization the biconditional is false in
both directions at `k = 2`** (`kfold_faithful_iff_affine_refuted`, `KfoldAffine.lean`; round-1
audit B1): `halfB = (0, ½, ½)` has faithful sets for both acts and is not affine,
`b4 = (0, ¼, ½)` is affine and has no pay-faithful set at `q' = ¼`.
Proved instance: `k = 2` (`kfold2_norm_faithful_both_iff_affine`), with the sharper per-act loci
`b_1 ∈ {½, 1}` for pay and `b_1 ∈ {0, ½}` for refuse (`kfold2_norm_pay_faithful_iff`,
`kfold2_norm_refuse_faithful_iff`); the data points `linearB 2` (both), `concaveB` (pay only),
`convexB 2` (refuse only, by the mirror), `halfB` (both, unnormalized).
Route for general `k` (hand-derived in repair round 1, not machine-checked): under `δ_pay` the
`(coin, r)`-law is `½` on `(T, −x)` and `½` on `(H, y)` (the all-pay leaf transfers with `b_k = 1`),
so a pay-faithful `E` contains the `T`-pay leaf, has mass `q'`, excludes every positive-mass
no-transfer leaf, and its transfer leaves carry mass `q'/2`; with `i_j` of the `C(k,j)` leaves at
`j` pays in `E`, dividing by `½ q'` gives
`q'^{k−1} + ∑_{j=1}^{k−1} i_j q'^{j−1} (1−q')^{k−j} b_j = 1` for every `q'` (a fixed subset
pattern serves infinitely many `q'` by pigeonhole, so this is a polynomial identity), and comparing
with `(q' + (1−q'))^{k−1}` in the Bernstein basis gives `i_j b_j = C(k−1, j−1)`; the mirror for
refuse gives `i'_j (1 − b_j) = C(k−1, j)`; since `i_j, i'_j ≤ C(k, j) = C(k−1, j−1) + C(k−1, j)`,
`b_j + (1 − b_j) = 1` forces `i_j = i'_j = C(k, j)`, i.e. `b_j = j/k`. What remains is the Lean
infrastructure: the leaf enumeration of `kfold k` for general `k` (the `k = 2` enumeration is
`Kfold.lean`'s `tLeaf`/`hLeaf`) and the pigeonhole/polynomial step.
Source: `faithful.md` Open 1 ("a faithful set exists for `a` iff the deviation law `μ_{δ_a}` is a
conditional of `μ_{C'}` on a union of leaves for all `q'`, which on nested fibers forces the coupling
to be affine in the number of paying draws"); dp-cf-153, dp-core-056
Kind: OPEN
Fidelity: variant: the conjecture "for both acts" restricted to normalized couplings (the
unnormalized form is refuted)
Hyps: (a) `2 ≤ k`, `0 < x`, `0 < y`; (a) `b 0 = 0`, `b k = 1` -/
theorem kfold_faithful_iff_affine_normalized_open (k : ℕ) (hk : 2 ≤ k) (x y : ℚ) (hx : 0 < x)
    (hy : 0 < y) (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) (hb0 : b 0 = 0) (hbk : b k = 1) :
    (∀ q' (h0 : 0 < q') (h1 : q' < 1), ∀ a : Act2, ∃ E : Finset (kfold k x y b hb).Leaves,
      LeafLawFaithfulWrt (kfold k x y b hb) (kfLabK k x y b hb) (procQ q' h0.le h1.le) () a E) ↔
    ∃ α β : ℚ, ∀ j ≤ k, b j = α * j + β := by
  sorry

/-- **OPEN — T18(a), the per-act locus for general `k`**: on the `k`-fold mugging with a
normalized coupling, a pay-faithful leaf-set exists for every full-support self-model iff for
every `j ∈ 1..k−1` some integer `i_j` with `C(k−1, j−1) ≤ i_j ≤ C(k, j)` has `i_j · b_j = C(k−1, j−1)`
— the coupling takes, at each level, one of finitely many rational values (the first-draw and
payoff-class sets are the two ends of the range). The `k = 2` instance is
`kfold2_norm_pay_faithful_iff` (`j = 1`: `1 ≤ i ≤ 2`, `i · b_1 = 1`, so `b_1 ∈ {1, ½}`). Route: the
docstring of `kfold_faithful_iff_affine_normalized_open` — the `⇐` direction is the construction
(the `T`-pay leaf, the all-pay transfer leaf and any `i_j` transfer leaves at each level `j`), the
`⇒` direction the Bernstein-basis comparison. The refuse locus is the mirror
(`C(k−1, j) ≤ i'_j ≤ C(k, j)`, `i'_j (1 − b_j) = C(k−1, j)`), not stated separately.
Source: `faithful.md` Open 1 (per-act form: "a faithful set exists for `a` iff …"); repair round 1
Kind: OPEN
Fidelity: variant: the per-act conjecture with the hand-derived locus in place of "affine"
Hyps: (a) `2 ≤ k`, `0 < x`, `0 < y`; (a) `b 0 = 0`, `b k = 1` -/
theorem kfold_pay_faithful_iff_locus_open (k : ℕ) (hk : 2 ≤ k) (x y : ℚ) (hx : 0 < x)
    (hy : 0 < y) (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) (hb0 : b 0 = 0) (hbk : b k = 1) :
    (∀ q' (h0 : 0 < q') (h1 : q' < 1), ∃ E : Finset (kfold k x y b hb).Leaves,
      LeafLawFaithfulWrt (kfold k x y b hb) (kfLabK k x y b hb) (procQ q' h0.le h1.le) () .a E) ↔
    ∀ j, 1 ≤ j → j < k → ∃ i : ℕ, (k - 1).choose (j - 1) ≤ i ∧ i ≤ k.choose j ∧
      (i : ℚ) * b j = ((k - 1).choose (j - 1) : ℚ) := by
  sorry

/-- Four sequential binary points with payoff table `v`. Source: `faithful.md` FA-14′(iv), Open 3.
Kind: D -/
def seq4 (v : Act2 → Act2 → Act2 → Act2 → ℚ) :
    Tree (Act2 × Act2 × Act2 × Act2) (Fin 4) (fun _ => Act2) ℚ :=
  .decision 0 fun a₁ => .decision 1 fun a₂ => .decision 2 fun a₃ => .decision 3 fun a₄ =>
    .leaf (a₁, a₂, a₃, a₄) (v a₁ a₂ a₃ a₄)

/-- The profile with the act `x` at the point `d` and `π` elsewhere. Source: none: infrastructure.
Kind: D -/
def single {ι : Type} [DecidableEq ι] (π : ι → Act2) (d : ι) (x : Act2) : ι → Act2 :=
  Function.update π d x

/-- **OPEN — T18(b), reading S on three points**: on `seq3 v` with a rational table, if `π*` is
optimal and every single deviation from `π*` is optimal (reading S of XC-14), then for small `ε`
every profile of best replies to `(π*)^ε` is optimal. The brute force over the `{0,1}` tables finds
no three-point failure (136 S-pairs); the general rational case is open. (The tie table of
`seq3_tie_refutation` fails the antecedent: `v(aab) = 0`.)
Source: `faithful.md` FA-13′ ("under reading S … the brute force finds no failure among 136
three-point and 32784 four-point S-pairs in `{0,1}` — but reading S is not rescued either: Open 3
records a five-point exact-tie witness"), Open 3 ("a proof that reading S holds for `n ≤ 4` in
general or a `{0,1,2}` four-point counterexample"); dp-cf-153
Kind: OPEN
Fidelity: exact
Hyps: (a) reading S for `π*` -/
theorem readingS_seq3_open (v : Act2 → Act2 → Act2 → ℚ) (π : Pt3 → Act2)
    (hπ : PureOptimal (seq3 v) π)
    (hS : ∀ d x, PureOptimal (seq3 v) (single π d x)) :
    ∃ ε₀ : ℚ, 0 < ε₀ ∧ ∀ ε (h0 : 0 < ε) (h1 : ε ≤ 1), ε < ε₀ →
      ∀ π' : Pt3 → Act2, (∀ d, π' d ∈ BR (tremble (Proc.ofFun π) ε h0.le h1) (seq3 v) d) →
        PureOptimal (seq3 v) π' := by
  sorry

/-- **OPEN — T18(b), reading S on four points**: as `readingS_seq3_open` on `seq4 v`.
Source: `faithful.md` Open 3 ("No four-point `{0,1}` S-pair fails (32784 checked)"); dp-cf-153
Kind: OPEN
Fidelity: exact
Hyps: (a) reading S for `π*` -/
theorem readingS_seq4_open (v : Act2 → Act2 → Act2 → Act2 → ℚ) (π : Fin 4 → Act2)
    (hπ : PureOptimal (seq4 v) π)
    (hS : ∀ d x, PureOptimal (seq4 v) (single π d x)) :
    ∃ ε₀ : ℚ, 0 < ε₀ ∧ ∀ ε (h0 : 0 < ε) (h1 : ε ≤ 1), ε < ε₀ →
      ∀ π' : Fin 4 → Act2, (∀ d, π' d ∈ BR (tremble (Proc.ofFun π) ε h0.le h1) (seq4 v) d) →
        PureOptimal (seq4 v) π' := by
  sorry

/-- **OPEN — T13(i)–(ii), general: a strict best reply to itself coordinates on every almost-fair
tree.** If `π*` strictly beats every single deviation at every queried point, then for small `ε`
the best replies to `(π*)^ε` are `{π*_d}` at every queried point (so `UDT_{s°,pol} = π*` on
`queried B` by `udtProc_polEv_eq_pure_iff`). Proved instance: two binary points
(`seq2_strict_bestReply`, explicit threshold); the Stag Hunt's `(S,S)` for every `0 < ε ≤ 1`
(`twoStag_udtProc_product` at `β = 1 − ε/2 > ⅓`). Route: `value_eq_product_mixture` makes
`V_B((π*)^ε[d↦a])` a
convex combination of pure values with weight `≥ (1−ε)^{|Q|} ≥ 1 − |Q|ε` on `π*[d↦a]`, so it is
within `2M|Q|ε` of `V_B(π*[d↦a])` (`M := max_π |V_B(π)|`); the strict gap `g` survives for
`ε < g/(4M|Q|+1)`.
Source: `faithful.md` FA-14′(i)–(ii); dp-cf-2-009
Kind: OPEN
Fidelity: exact
Hyps: (a) `AlmostFair B`; (a) `π*` a strict best reply to itself at every queried point -/
theorem strict_bestReply_open {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
    [Fintype ι] (B : Tree Ω ι (fun _ => Act2) ℚ) (hB : AlmostFair B) (π : ι → Act2)
    (hstrict : ∀ d ∈ queried B, ∀ a, a ≠ π d →
      value (Proc.ofFun (single π d a)) B < value (Proc.ofFun π) B) :
    ∃ ε₀ : ℚ, 0 < ε₀ ∧ ∀ ε (h0 : 0 < ε) (h1 : ε ≤ 1), ε < ε₀ →
      ∀ d ∈ queried B, BR (tremble (Proc.ofFun π) ε h0.le h1) B d = {π d} := by
  sorry

end open_

end Cleanroom.Decision.DpFaithfulUdt
