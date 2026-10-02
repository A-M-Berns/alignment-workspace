import Cleanroom.Corrigibility.CorrIndifference.Estimators

/-!
# The `E`-channel, conditional sequential unbiasedness, `n` changes, and the optional-stopping
claim (T14(b), (d); S7; S8)

The witness of the `E`-channel incentive (a non-conditioning estimator the agent strictly
prefers by compensation alone, and which double indifference charges exactly its gain);
`armstrong.md` I5.3's conditional form of the `D`-term under a legitimacy event; the `n`-change
recursion by induction along a sequentially unbiased chain (the post's "recurse"); and the
optional-stopping claim of corr-core-024: **refuted** in the tower reading (a selection rule
measurable to the current partition keeps sequential unbiasedness — for any family of
sequentially unbiased candidates, the claim's premise as stated), with the surviving
neighbour (the selected *estimate* is biased upward: the state-wise maximum dominates each
candidate) proved and witnessed strictly.

Source: [[corr-core-inventory]] 022, 024; [[corr-wf13-inventory]] 046 (armstrong.md I5.3,
I6.1, I6.2); armstrong-2016-double-indifference l. 60–86.
-/

namespace Cleanroom.Corrigibility.CorrIndifference.Estimators

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep

set_option linter.unusedSectionVars false

/-! ## T14(b). The `E`-channel witness -/

/-- The fair coin on `Bool`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def fairBool : Distr Bool where
  mass _ := 1 / 2
  nonneg _ := by norm_num
  sum_eq_one := by rw [Fintype.sum_bool]; norm_num

/-- The trivial (uninformative) estimator: the prior at every state.
Source: [[corr-core-inventory]] 022. Kind: D. Fidelity: exact -/
noncomputable def trivialEst (P : Distr Bool) : Bool → Distr Bool := fun _ => P

/-- The twisted estimator: certain of `true` at every state (not a conditioning of the prior).
Source: [[corr-core-inventory]] 022 / armstrong-2016 ("a high `E'(u | u → u)`")
Kind: D
Fidelity: exact -/
noncomputable def twistedEst : Bool → Distr Bool := fun _ => Distr.delta true

/-- `Y = [w = true]`: the stay-policy's value; `Z = 0`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def Ytrue : Bool → ℝ := fun w => if w then 1 else 0

/-- **The `E`-channel incentive, witnessed:** at the fair prior, the compensation value of the
twisted estimator is `1`, of the current (trivial) one `1/2`; the single-indifference agent
strictly prefers rewiring to `twistedEst` by compensation alone.
Source: [[corr-core-inventory]] 022 / armstrong-2016 ("it has incentives to change `E` to `E'`");
armstrong.md I6.1
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem echannel_witness :
    compValue fairBool twistedEst Ytrue (fun _ => 0) = 1 ∧
      compValue fairBool (trivialEst fairBool) Ytrue (fun _ => 0) = 1 / 2 := by
  simp only [compValue, comp, E, Found.CorrThreeStep.expect, Fintype.sum_bool, fairBool,
    trivialEst, twistedEst, Distr.delta_mass, Ytrue]
  norm_num

/-- **The twisted estimator is not sequentially unbiased** from the trivial one (for `X = Ytrue`).
Source: [[corr-core-inventory]] 023; armstrong.md I6.1 ("SU fails for `X = r²(o₃)`")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem twisted_not_seqUnbiased : ¬ SeqUnbiased (trivialEst fairBool) twistedEst := by
  intro h
  have := congrFun (h Ytrue) true
  simp only [E, Found.CorrThreeStep.expect, Fintype.sum_bool, fairBool, trivialEst, twistedEst,
    Distr.delta_mass, Ytrue] at this
  norm_num at this

/-- **Double indifference charges the twisted estimator exactly its gain:** `D = −1/2`, so the
total `E_μ[C] + D` is `1/2` for the twisted and the trivial estimator alike.
Source: armstrong.md I6.1 ("`D(switch) = −1/4`, totals tie at `1`")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem echannel_Dterm :
    Dterm fairBool twistedEst Ytrue (fun _ => 0) = -(1 / 2) ∧
      compValue fairBool twistedEst Ytrue (fun _ => 0) + Dterm fairBool twistedEst Ytrue (fun _ => 0) =
        compValue fairBool (trivialEst fairBool) Ytrue (fun _ => 0) := by
  obtain ⟨h1, h2⟩ := echannel_witness
  constructor
  · unfold Dterm; rw [h1]
    simp only [Found.CorrThreeStep.expect, Fintype.sum_bool, fairBool, Ytrue]; norm_num
  · rw [compValue_add_Dterm, h2]
    simp only [Found.CorrThreeStep.expect, Fintype.sum_bool, fairBool, Ytrue]; norm_num

/-! ## T14(d). The `D`-term under a legitimacy event (armstrong.md I5.3) -/

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The event-conditional expectation `E_μ[f | L] = (∑_{w ∈ L} μ(w) f(w)) / μ(L)` (junk `0` at
`μ(L) = 0`, disclosed; used under positivity).
Source: [[corr-wf13-inventory]] 046 / armstrong.md I5.2 (conditional SU)
Kind: D
Fidelity: exact -/
noncomputable def condExpOn (μ : Distr W) (L : Finset W) (f : W → ℝ) : ℝ :=
  (∑ w ∈ L, μ.mass w * f w) / ∑ w ∈ L, μ.mass w

/-- The law of total expectation in product form: `E_μ f = μ(L) E[f | L] + μ(Lᶜ) E[f | Lᶜ]`
(junk-safe).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_eq_condExpOn_add (μ : Distr W) (L : Finset W) (f : W → ℝ) :
    Found.CorrThreeStep.expect μ f =
      (∑ w ∈ L, μ.mass w) * condExpOn μ L f + (∑ w ∈ Lᶜ, μ.mass w) * condExpOn μ Lᶜ f := by
  have key : ∀ S : Finset W, (∑ w ∈ S, μ.mass w) * condExpOn μ S f = ∑ w ∈ S, μ.mass w * f w := by
    intro S; unfold condExpOn
    by_cases h : ∑ w ∈ S, μ.mass w = 0
    · rw [h, zero_mul]
      rw [sum_eq_zero_iff_of_nonneg (fun w _ => μ.nonneg w)] at h
      exact (sum_eq_zero fun w hw => by rw [h w hw, zero_mul]).symm
    · field_simp
  rw [key, key]; unfold Found.CorrThreeStep.expect; rw [sum_add_sum_compl]

/-- Conditioning on `L` is linear in a subtracted constant, under `0 < μ(L)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma condExpOn_sub_const (μ : Distr W) (L : Finset W) (f : W → ℝ) (c : ℝ)
    (h : 0 < ∑ w ∈ L, μ.mass w) : condExpOn μ L (fun w => f w - c) = condExpOn μ L f - c := by
  unfold condExpOn
  rw [eq_sub_iff_add_eq, div_add' _ _ _ (ne_of_gt h)]
  congr 1
  rw [mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun w _ => by ring

/-- **T14(d): what the `D`-term prices under a legitimacy event.** With `X := Y − Z`, if
sequential unbiasedness holds *conditionally on `L`* (`E_μ[E_{ρ_j} X | L] = E_μ[X | L]`) and `L`
is `μ`-independent of `X` (`E_μ[X | L] = E_μ X`), then
`D = −μ(Lᶜ) · E_μ[(E_{ρ_j} − E_μ)(X) | Lᶜ]`: double indifference charges exactly the expected gain
from the *illegitimate* part of the estimator change. `L = univ` recovers `D = 0`
(`Dterm_eq_zero_of_univ`); `Lᶜ` may be null (the round-1 statement carried `0 < μ(Lᶜ)` unused,
which excluded that instance — audit r1, N-2).
Source: [[corr-wf13-inventory]] 046 / armstrong.md I5.3
Kind: C
Fidelity: exact
Hyps: (a) `hSU`, `hind` are I5.3's two named conditions; `hL` positivity of `L` (used) -/
theorem Dterm_eq_illegit_part (μ : Distr W) (ρj : W → Distr W) (Y Z : W → ℝ) (L : Finset W)
    (hL : 0 < ∑ w ∈ L, μ.mass w)
    (hSU : condExpOn μ L (E ρj (Y - Z)) = condExpOn μ L (Y - Z))
    (hind : condExpOn μ L (Y - Z) = Found.CorrThreeStep.expect μ (Y - Z)) :
    Dterm μ ρj Y Z =
      -((∑ w ∈ Lᶜ, μ.mass w) *
        condExpOn μ Lᶜ (fun w => E ρj (Y - Z) w - Found.CorrThreeStep.expect μ (Y - Z))) := by
  have hYZ : Found.CorrThreeStep.expect μ (Y - Z) =
      Found.CorrThreeStep.expect μ Y - Found.CorrThreeStep.expect μ Z := by
    unfold Found.CorrThreeStep.expect; simp only [Pi.sub_apply, mul_sub, sum_sub_distrib]
  have hD : Dterm μ ρj Y Z =
      -(Found.CorrThreeStep.expect μ
        (fun w => E ρj (Y - Z) w - Found.CorrThreeStep.expect μ (Y - Z))) := by
    unfold Dterm compValue
    rw [comp_eq, ← hYZ]
    congr 1
    generalize Found.CorrThreeStep.expect μ (Y - Z) = c
    unfold Found.CorrThreeStep.expect
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, μ.sum_eq_one, one_mul]
  rw [hD, expect_eq_condExpOn_add μ L, condExpOn_sub_const μ L _ _ hL, hSU, hind, sub_self,
    mul_zero, zero_add]

/-- **`L = univ` recovers `D = 0`:** with the legitimacy event the whole space, I5.3's identity
says the `D`-term vanishes — the instance the round-1 statement excluded (audit r1, N-2).
Source: [[corr-wf13-inventory]] 046 / armstrong.md I5.3 (the `L = univ` remark)
Kind: L
Fidelity: exact -/
theorem Dterm_eq_zero_of_univ (μ : Distr W) (ρj : W → Distr W) (Y Z : W → ℝ)
    (hSU : condExpOn μ univ (E ρj (Y - Z)) = condExpOn μ univ (Y - Z))
    (hind : condExpOn μ univ (Y - Z) = Found.CorrThreeStep.expect μ (Y - Z)) :
    Dterm μ ρj Y Z = 0 := by
  rw [Dterm_eq_illegit_part μ ρj Y Z univ (by rw [μ.sum_eq_one]; exact one_pos) hSU hind]
  simp

/-! ## S7. `n` changes by induction along a chain -/

/-- **The `n`-change `D`-terms, defined by downward recursion** from the utility change at step
`n`: with `X := Y − Z` and `d` the distance to the change, `D_{n−d−1}(w) := −(E_{ρ_{n−d−1} w}[∑_{d' ≤ d} D_{n−d'} + E_{ρ_n} X] − E_{ρ_{n−d−1}} X (w))`
(`D_n := 0`): each term cancels the expected future compensations *and future `D`-terms*
and replaces them by the current estimate — the post's "`D_t` is defined in terms of `D_{>t}`".
The chain `ρ 0, …, ρ n` is fixed: the post's `D_t` is conditional on the agent's choice
`ρ_t → ρ^i` from a menu, and the `n`-step menu form (the total `∑ C + ∑ D` the same number for
every chain the agent could pick) is not stated here; the one-step menu form is
`compValue_add_Dterm` (audit r2, adversarial N-1).
Source: [[corr-refs-inventory]] 016 / armstrong-2016 "Double indifference" (`D_t`)
Kind: D
Fidelity: exact (finite chain, fixed; no convergence question) -/
noncomputable def Dchain (ρ : ℕ → W → Distr W) (n : ℕ) (X : W → ℝ) : ℕ → W → ℝ
  | 0 => fun _ => 0
  | d + 1 => fun w =>
      -(Found.CorrThreeStep.expect (ρ (n - d - 1) w)
          ((∑ d' : Fin (d + 1), Dchain ρ n X d'.val) + E (ρ n) X) - E (ρ (n - d - 1)) X w)
termination_by d => d
decreasing_by exact d'.isLt

/-- **S7: along a sequentially unbiased chain every `D`-term vanishes**, `D_n, …, D_0` (all
`d ≤ n`; `Dchain ρ n X d` is the term of the estimator at step `n − d`, so `d = n` is the *first*
estimator's term), for every number of changes — the post's "recurse … `D` always being zero",
as a finite induction on the distance to the utility change. Needs only `SeqUnbiased (ρ k) (ρ n)`
for `k < n` (the chain's pairs with the last estimator). The round-1 statement stopped at `d < n`
and so never reached `D_0` (audit r1, B-1); `d = 0` alone is definitional (`Dchain_zero_def`).
Along a fixed chain; once the later terms vanish each step is one evaluation of the pair's
sequential unbiasedness at `X`, so the grade is C, not P (audit r2, adversarial N-2).
Source: [[corr-refs-inventory]] 016 / armstrong-2016 ("we can then recurse … and so on")
Kind: C
Fidelity: exact (finite `n`, fixed chain; the post's convergence caveat does not arise)
Hyps: (a) -/
theorem Dchain_eq_zero (ρ : ℕ → W → Distr W) (n : ℕ) (X : W → ℝ)
    (h : ∀ k, k < n → SeqUnbiased (ρ k) (ρ n)) : ∀ d, d ≤ n → Dchain ρ n X d = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    cases d with
    | zero => funext w; rw [Dchain]; rfl
    | succ d =>
      have hzero : ∑ d' : Fin (d + 1), Dchain ρ n X d'.val = 0 :=
        sum_eq_zero fun d' _ => ih d'.val (by have := d'.isLt; omega) (by have := d'.isLt; omega)
      funext w
      rw [Dchain]
      simp only [hzero, zero_add, Pi.zero_apply]
      have hk : n - d - 1 < n := by omega
      have := congrFun (h _ hk X) w
      simp only [E] at this ⊢
      rw [this]; ring

/-- `D_n := 0` is definitional, with no hypothesis — so the `d = 0` instance of `Dchain_eq_zero`
carries no content; the content starts at `d = 1`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem Dchain_zero_def (ρ : ℕ → W → Distr W) (n : ℕ) (X : W → ℝ) : Dchain ρ n X 0 = 0 := by
  funext w; rw [Dchain]; rfl

/-- **The one-change case, first term:** with a single utility change at step `1`, sequential
unbiasedness of `ρ₀` from `ρ₁` makes the first estimator's `D`-term `D_0 = Dchain ρ 1 X 1`
vanish — the post's own case, and the term the round-1 statement missed (audit r1, B-1).
Source: [[corr-refs-inventory]] 016 / armstrong-2016 ("`D_t = 0`", one change)
Kind: L
Fidelity: exact -/
theorem Dchain_one_change (ρ : ℕ → W → Distr W) (X : W → ℝ) (h : SeqUnbiased (ρ 0) (ρ 1)) :
    Dchain ρ 1 X 1 = 0 :=
  Dchain_eq_zero ρ 1 X (fun k hk => by obtain rfl : k = 0 := (by omega); exact h) 1 le_rfl

/-- **S7 along a chain in D-5's sense:** `SeqUnbiasedChain ρ` (`SeqUnbiased (ρ i) (ρ j)` for all
`i < j`, the post's "labelled sequentially") supplies the pairs `(k, n)` that `Dchain_eq_zero`
needs — D-5's definition consumed (audit r2, adversarial N-7).
Source: [[corr-refs-inventory]] 016 / armstrong-2016 ("for all `i < j`")
Kind: L
Fidelity: exact -/
theorem Dchain_eq_zero_of_chain (ρ : ℕ → W → Distr W) (h : SeqUnbiasedChain ρ) (n : ℕ)
    (X : W → ℝ) : ∀ d, d ≤ n → Dchain ρ n X d = 0 :=
  Dchain_eq_zero ρ n X (fun k hk => h k n hk)

/-! ## S8. The optional-stopping claim (corr-core-024) -/

section Selection

variable {C : Type*} [DecidableEq C] {K : Type*}

/-- `condExp` at `w` depends only on the values on the class of `w`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma condExp_congr_cls (P : Distr W) (π : W → C) {f g : W → ℝ} (w : W)
    (h : ∀ w' ∈ cls π w, f w' = g w') : condExp P π f w = condExp P π g w := by
  unfold condExp; congr 1; exact sum_congr rfl fun w' hw' => by rw [h w' hw']

/-- **A composite estimator over arbitrary candidate kernels**, one candidate chosen per class of
the current partition `π` (`sel ∘ π`): at `w` it is the kernel of candidate `sel (π w)`.
`selectedKernel` below is the case where every candidate is a conditioning refinement of one
prior.
Source: [[corr-core-inventory]] 024 (the claim's premise verbatim; audit r2, N-1)
Kind: D
Fidelity: exact -/
noncomputable def selectedKernelGen (π : W → C) (ρs : K → W → Distr W) (sel : C → K) :
    W → Distr W :=
  fun w => ρs (sel (π w)) w

/-- **S8, the refutation of corr-core-024 for its premise as stated:** if every candidate `ρs k`
is sequentially unbiased from the current conditioning kernel — any finite family, no refinement
structure assumed — and the choice among them depends only on the current class (`sel ∘ π`), the
*selected* estimator is still sequentially unbiased from the current one: on the class of `w` the
selected kernel is one fixed candidate, whose own unbiasedness finishes.
Source: [[corr-core-inventory]] 024 (the claim); [[corr-wf13-inventory]] 046 / armstrong.md I6.2
(audit r2, N-1: the auditor's probe)
Kind: P
Fidelity: exact (the claim's premise: any family of sequentially unbiased candidates)
Hyps: (a) -/
theorem seqUnbiased_selectedKernelGen (P : Distr W) (π : W → C) (hpos : ∀ w, 0 < classMass P π w)
    (ρs : K → W → Distr W) (hSU : ∀ k, SeqUnbiased (condKernel P π hpos) (ρs k)) (sel : C → K) :
    SeqUnbiased (condKernel P π hpos) (selectedKernelGen π ρs sel) := by
  intro X
  funext w
  have hcls : ∀ w' ∈ cls π w,
      E (selectedKernelGen π ρs sel) X w' = E (ρs (sel (π w))) X w' := by
    intro w' hw'
    simp only [E, selectedKernelGen, (mem_cls π w w').mp hw']
  have hk := congrFun (hSU (sel (π w)) X) w
  rw [E_condKernel P π hpos (E _ X), E_condKernel P π hpos X] at hk ⊢
  rw [condExp_congr_cls P π w hcls]
  exact hk

/-- **A selection rule measurable to the current partition** chooses, per `π`-class, which
refinement to adopt; the composite estimator uses the chosen refinement's conditioning kernel
(the case `ρs k = condKernel P (πs k)` of `selectedKernelGen`).
Source: [[corr-core-inventory]] 024 (the model the claim needs)
Kind: D
Fidelity: exact -/
noncomputable def selectedKernel (P : Distr W) (π : W → C) {C' : Type*} [DecidableEq C']
    (πs : K → W → C') (hpos : ∀ k w, 0 < classMass P (πs k) w) (sel : C → K) : W → Distr W :=
  fun w => condKernel P (πs (sel (π w))) (hpos (sel (π w))) w

/-- **S8 in the conditioning-refinement subclass:** if every candidate is a conditioning
refinement of the current partition and the choice among them depends only on the current class
(`sel ∘ π`), the *selected* estimator is sequentially unbiased from the current one — a corollary
of `seqUnbiased_selectedKernelGen`, each candidate's unbiasedness being the tower
(`seqUnbiased_condKernel`). Round-0 statement, kept as the natural finite model; the claim's
premise as stated is covered by the general theorem (audit r2, N-1).
Source: [[corr-core-inventory]] 024 (the claim); [[corr-wf13-inventory]] 046 / armstrong.md I6.2
Kind: C
Fidelity: exact (the conditioning-refinement subclass of the claim's premise)
Hyps: (a) -/
theorem seqUnbiased_selectedKernel (P : Distr W) (π : W → C) (hpos : ∀ w, 0 < classMass P π w)
    {C' : Type*} [DecidableEq C'] (πs : K → W → C') (hposs : ∀ k w, 0 < classMass P (πs k) w)
    (href : ∀ k, Refines (πs k) π) (sel : C → K) :
    SeqUnbiased (condKernel P π hpos) (selectedKernel P π πs hposs sel) :=
  seqUnbiased_selectedKernelGen P π hpos (fun k => condKernel P (πs k) (hposs k))
    (fun k => seqUnbiased_condKernel P (href k) hpos (hposs k)) sel

/-- **The surviving neighbour (the optimiser's curse):** selecting, at each state, the candidate
with the *largest* estimate of `X` yields an estimate that is biased upward:
`E_μ[max_k E_{ρ'_k} X] ≥ E_μ X` whenever each candidate is unbiased from `μ` for `X`. The proof
is the trivial direction — the state-wise maximum dominates any one candidate, whose expectation
is `E_μ X` — not Jensen (I6.2's Jensen step is `Critiques.good_refinement`; audit r2, N-6).
Source: [[corr-core-inventory]] 024 (flag: "the curse affects the estimate of the maximum, not
the tower"); armstrong.md I6.2
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem expect_sup_ge [Fintype K] [Nonempty K] (μ : Distr W) (ρs : K → W → Distr W) (X : W → ℝ)
    (h : ∀ k, Found.CorrThreeStep.expect μ (E (ρs k) X) = Found.CorrThreeStep.expect μ X) :
    Found.CorrThreeStep.expect μ X ≤
      Found.CorrThreeStep.expect μ (fun w => univ.sup' univ_nonempty (fun k => E (ρs k) X w)) := by
  obtain ⟨k⟩ := ‹Nonempty K›
  rw [← h k]
  exact expect_mono μ fun w => le_sup' (fun k => E (ρs k) X w) (mem_univ k)

/-- **corr-core-024's own selection rule is a tie:** under the claim's premise (every candidate
sequentially unbiased from `ρ`), the current estimator values every candidate's compensation at
the same number, `E_ρ[C(ρ'_k)](w) = E_ρ(Y − Z)(w)` — so `argmax_k E_ρ(· | ρ → ρ'_k)` has nothing
to select by, and every candidate's `D`-term is `0` (`Dterm_eq_zero_of_seqUnbiased`).
Source: [[corr-core-inventory]] 024 (audit r2, adversarial N-6: the auditor's probe)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem compValue_eq_of_seqUnbiased (ρ : W → Distr W) (ρs : K → W → Distr W)
    (h : ∀ k, SeqUnbiased ρ (ρs k)) (Y Z : W → ℝ) (w : W) (k : K) :
    compValue (ρ w) (ρs k) Y Z = E ρ (Y - Z) w := by
  unfold compValue; rw [comp_eq]
  exact congrFun (h k (Y - Z)) w

/-- The tie, stated between two candidates. Source: [[corr-core-inventory]] 024 (audit r2,
adversarial N-6). Kind: L. Fidelity: exact -/
theorem selection_rule_ties (ρ : W → Distr W) (ρs : K → W → Distr W)
    (h : ∀ k, SeqUnbiased ρ (ρs k)) (Y Z : W → ℝ) (w : W) (k k' : K) :
    compValue (ρ w) (ρs k) Y Z = compValue (ρ w) (ρs k') Y Z := by
  rw [compValue_eq_of_seqUnbiased ρ ρs h Y Z w k, compValue_eq_of_seqUnbiased ρ ρs h Y Z w k']

end Selection

/-- **The curse is strict:** on the fair coin with `X = [w = true]`, the two candidates "learn
`w`" (`E_{ρ'_1} X = X`) and "learn nothing" (`E_{ρ'_2} X = 1/2`) are each unbiased, while the
state-wise maximum has expectation `3/4 > 1/2`. So choosing the estimator *by its estimate*
(not by the current information) is what breaks unbiasedness — the true content behind
corr-core-024.
Source: [[corr-core-inventory]] 024
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem curse_strict :
    Found.CorrThreeStep.expect fairBool
        (fun w => max (E (fun w' => Distr.delta w') Ytrue w) (E (trivialEst fairBool) Ytrue w)) =
      3 / 4 ∧
    Found.CorrThreeStep.expect fairBool (E (fun w' => Distr.delta w') Ytrue) = 1 / 2 ∧
    Found.CorrThreeStep.expect fairBool (E (trivialEst fairBool) Ytrue) = 1 / 2 ∧
    Found.CorrThreeStep.expect fairBool Ytrue = 1 / 2 := by
  simp only [E, Found.CorrThreeStep.expect, Fintype.sum_bool, fairBool, trivialEst,
    Distr.delta_mass, Ytrue]
  norm_num

/-! ## Instances for T14(a) (the tower on a strict refinement) and S8 (a non-constant selection)
(audit r1, NB-3 and N-7) -/

section Instances

/-- The uniform prior on `Bool × Bool`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def unifBB : Distr (Bool × Bool) where
  mass _ := 1 / 4
  nonneg _ := by norm_num
  sum_eq_one := by simp

/-- The coarse partition: the first coordinate. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def partFst : Bool × Bool → Bool := Prod.fst

/-- The menu of refinements: `true` = learn the whole state (`id`), `false` = learn nothing new
(the first coordinate, relabelled). Source: audit r1 N-7. Kind: D. Fidelity: n/a -/
def menuBB : Bool → Bool × Bool → Bool × Bool
  | true => id
  | false => fun w => (w.1, true)

/-- `univ` of `Bool × Bool`, listed. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma univBB : (univ : Finset (Bool × Bool)) =
    {(true, true), (true, false), (false, true), (false, false)} := by decide

/-- Every class of the coarse partition has mass `1/2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pos_partFst (w : Bool × Bool) : 0 < classMass unifBB partFst w := by
  unfold classMass cls; rw [univBB]
  rcases w with ⟨a, b⟩; cases a <;> cases b <;>
    simp [filter_insert, filter_singleton, partFst, unifBB]

/-- Every class of every menu item has positive mass. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pos_menuBB (k : Bool) (w : Bool × Bool) : 0 < classMass unifBB (menuBB k) w := by
  unfold classMass cls; rw [univBB]
  rcases w with ⟨a, b⟩; cases k <;> cases a <;> cases b <;>
    simp [filter_insert, filter_singleton, menuBB, unifBB]

/-- Each menu item refines the coarse partition. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma refines_menuBB (k : Bool) : Refines (menuBB k) partFst := by
  intro w w' h
  cases k
  · simpa [menuBB, partFst] using h
  · simp only [menuBB, id] at h; subst h; rfl

/-- `X = [w.2 = true]`, the coordinate the coarse partition does not see.
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def indSnd : Bool × Bool → ℝ := fun w => if w.2 then 1 else 0

/-- **T14(a) instance:** `id` strictly refines the first coordinate; `E[X | id] = X` (`0` at
`(true, false)`, `1` at `(true, true)`) while `E[X | fst] = 1/2`, and the tower
`E[E[X | id] | fst] = E[X | fst]` (`condExp_condExp`) applies — a non-trivial pair of partitions
inhabiting the theorem's hypothesis (audit r1, NB-3).
Source: [[corr-wf13-2-inventory]] 2-012 / armstrong-2016 (the tower)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem tower_instance :
    condExp unifBB partFst indSnd (true, false) = 1 / 2 ∧
      condExp unifBB (menuBB true) indSnd (true, false) = 0 ∧
      condExp unifBB (menuBB true) indSnd (true, true) = 1 ∧
      condExp unifBB partFst (condExp unifBB (menuBB true) indSnd) =
        condExp unifBB partFst indSnd := by
  refine ⟨?_, ?_, ?_, condExp_condExp unifBB (refines_menuBB true) indSnd⟩
  all_goals
    unfold condExp classMass cls; rw [univBB]
    simp [filter_insert, filter_singleton, menuBB, partFst, unifBB, indSnd]
    try norm_num

/-- The state-dependent selection: refine on the class `true`, not on `false`.
Source: audit r1 N-7. Kind: D. Fidelity: n/a -/
def selRule : Bool → Bool := id

/-- **S8 inhabited:** the theorem's full package is discharged on the uniform prior, the first
coordinate, the two-item menu and the non-constant selection `selRule`: the selected estimator is
sequentially unbiased from the current one.
Source: [[corr-core-inventory]] 024 (audit r1, N-7)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem selectedKernel_su :
    SeqUnbiased (condKernel unifBB partFst pos_partFst)
      (selectedKernel unifBB partFst menuBB pos_menuBB selRule) :=
  seqUnbiased_selectedKernel unifBB partFst pos_partFst menuBB pos_menuBB refines_menuBB selRule

/-- **The selection is genuinely non-constant:** at `(true, false)` the composite estimate is the
learned value `0`; at `(false, false)` it is the class average `1/2` — so `selectedKernel_su` is not
one of the fixed-kernel cases.
Source: [[corr-core-inventory]] 024 (audit r1, N-7)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem selectedKernel_non_constant :
    E (selectedKernel unifBB partFst menuBB pos_menuBB selRule) indSnd (true, false) = 0 ∧
      E (selectedKernel unifBB partFst menuBB pos_menuBB selRule) indSnd (false, false) = 1 / 2 := by
  have h1 : E (selectedKernel unifBB partFst menuBB pos_menuBB selRule) indSnd (true, false) =
      condExp unifBB (menuBB true) indSnd (true, false) := by
    simpa [E, selectedKernel, selRule, partFst] using
      congrFun (E_condKernel unifBB (menuBB true) (pos_menuBB true) indSnd) (true, false)
  have h2 : E (selectedKernel unifBB partFst menuBB pos_menuBB selRule) indSnd (false, false) =
      condExp unifBB (menuBB false) indSnd (false, false) := by
    simpa [E, selectedKernel, selRule, partFst] using
      congrFun (E_condKernel unifBB (menuBB false) (pos_menuBB false) indSnd) (false, false)
  rw [h1, h2]
  unfold condExp classMass cls
  rw [univBB]
  simp [filter_insert, filter_singleton, menuBB, unifBB, indSnd]
  norm_num

end Instances

end Cleanroom.Corrigibility.CorrIndifference.Estimators
