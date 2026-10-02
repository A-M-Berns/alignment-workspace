import Cleanroom.Found.CorrThreeStep.Setting
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# `corr-landscape` — `Legitimizing`: S11, the three-valued legitimizing relation (T9, stretch)

P9 ([[corr-wf14-inventory]] 122): the overseer's verdict `V = φ(E, S)` on a finite product `E × S`
(evidence × the agent's state) with a joint law `μ`. Three classes:

* **inert** — `V` is a function of `S` alone (`σ(S)`-measurable): conditioning on `V` jointly with `S` is
  a null update. Theorem (`inert_null_update`): for every event `X` and every state `s` with `V = g s`, the
  mass-weighted sum over `{S = s, V = v}` equals the one over `{S = s}` (and is `0` for `v ≠ g s`) — in
  product form, no ratio.
* **legitimizing** — conditioning on `V` strictly lowers the expected quadratic score about a target `X`
  (`legitimizing`, finite sums): the posterior means `E[X ∣ V = v]` beat the prior mean `E[X]`.
* **delegitimizing** — the reflection equation `E[X ∣ V = v] = v` fails on some attained `v`, for the
  verdict read as a forecast of `X` (`delegitimizing`).

N+: one `E × S` instance of each class on `Bool × Bool` (`inert_instance`, `legitimizing_instance`,
`delegitimizing_instance`). The cumulative caveat (A11.3, O4) is recorded as text in the findings: a
per-round defect measures only the marginal `S`-dependence; no Lean.

Register: the three classes are the source's (CLAUDE) construal of v1 §2.11's relation; "inert" is
the source's name. The quadratic score is the proper score chosen here (the source says "proper-score
accuracy", unspecified).
-/

namespace Cleanroom.Corrigibility.CorrLandscape

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

set_option linter.unusedSectionVars false

namespace Legitimizing

variable {E S V : Type} [Fintype E] [Fintype S] [DecidableEq E] [DecidableEq S] [DecidableEq V]

/-- **Inert**: the verdict is a function of the agent's state alone.
Source: [[corr-wf14-inventory]] 122 / approval-final.md S11(a), P9 ("the `σ(S_t)`-measurable part is
inert")
Kind: D
Fidelity: exact -/
def inert (φ : E → S → V) : Prop := ∃ g : S → V, ∀ e s, φ e s = g s

/-- The mass-weighted sum of `X` over `{S = s, V = v}` (product form).
Source: approval-final.md P9. Kind: D. Fidelity: exact -/
def condSumSV (μ : Distr (E × S)) (φ : E → S → V) (X : E × S → ℝ) (s : S) (v : V) : ℝ :=
  ∑ p ∈ univ.filter (fun p : E × S => p.2 = s ∧ φ p.1 p.2 = v), μ.mass p * X p

/-- The mass-weighted sum of `X` over `{S = s}`.
Source: approval-final.md P9. Kind: D. Fidelity: exact -/
def condSumS (μ : Distr (E × S)) (X : E × S → ℝ) (s : S) : ℝ :=
  ∑ p ∈ univ.filter (fun p : E × S => p.2 = s), μ.mass p * X p

/-- **An inert verdict is a null update**: conditioning on `V` jointly with `S` changes nothing — on the
attained value `v = g s` the two sums agree, on any other `v` the event is empty.
Source: [[corr-wf14-inventory]] 122 / approval-final.md S11(a), P9 ("reflecting toward it is a null
update")
Kind: L
Fidelity: exact (product form)
Hyps: (a) only -/
theorem inert_null_update (μ : Distr (E × S)) (φ : E → S → V) (hφ : inert φ) (X : E × S → ℝ) (s : S) :
    ∃ g : S → V, (∀ e s', φ e s' = g s') ∧ condSumSV μ φ X s (g s) = condSumS μ X s ∧
      ∀ v, v ≠ g s → condSumSV μ φ X s v = 0 := by
  obtain ⟨g, hg⟩ := hφ
  refine ⟨g, hg, ?_, ?_⟩
  · unfold condSumSV condSumS
    refine sum_congr ?_ fun _ _ => rfl
    ext ⟨e, s'⟩
    simp only [mem_filter, mem_univ, true_and, hg]
    constructor
    · exact fun h => h.1
    · intro h; exact ⟨h, by rw [h]⟩
  · intro v hv
    unfold condSumSV
    apply sum_eq_zero
    intro ⟨e, s'⟩ hp
    simp only [mem_filter, mem_univ, true_and, hg] at hp
    exact absurd (hp.1 ▸ hp.2) (Ne.symm hv)

/-- The expected quadratic score of a forecast `f` of the target `X`: `E[(X − f)²]`.
Source: approval-final.md S11(a) ("raises expected accuracy"); the proper score chosen here
Kind: D
Fidelity: variant: the quadratic score for the source's unspecified proper score -/
noncomputable def quadScore (μ : Distr (E × S)) (X f : E × S → ℝ) : ℝ := expect μ (fun p => (X p - f p) ^ 2)

/-- The verdict-conditional mean of `X` as a forecast: `E[X 𝟙[V = v]]/P(V = v)` at the attained verdict.
A named real, junk at mass `0`; used only inside the two predicates below, which quantify over
positive-mass verdicts.
Source: approval-final.md S11(a)
Kind: D
Fidelity: exact under positive verdict mass -/
noncomputable def condMean (μ : Distr (E × S)) (φ : E → S → V) (X : E × S → ℝ) (p : E × S) : ℝ :=
  (∑ q ∈ univ.filter (fun q : E × S => φ q.1 q.2 = φ p.1 p.2), μ.mass q * X q) /
    ∑ q ∈ univ.filter (fun q : E × S => φ q.1 q.2 = φ p.1 p.2), μ.mass q

/-- **Legitimizing**: conditioning on the verdict strictly lowers the expected quadratic score about the
target, against the prior mean. **The three classes overlap as formalized**: the baseline here is the
*unconditional* mean `E[X]`, not what `P_t` already knows from its own state `S`, so a verdict that is a
function of `S` alone (inert) is also legitimizing whenever `S` is informative about the target
(`inert_and_legitimizing`); `inert`/`legitimizing`/`delegitimizing` are not a trichotomy. The source's
"carries no information for `P_t`" is relative to `S`; the `S`-relative baseline is the natural repair
(condition on `V` jointly with `S`, as `inert_null_update` does) and is not built here (audit r1, N5).
Source: [[corr-wf14-inventory]] 122 / approval-final.md S11(a) ("*legitimizing* (raises expected
accuracy)")
Kind: D
Fidelity: variant (quadratic score; unconditional baseline, so the classes overlap) -/
def legitimizing (μ : Distr (E × S)) (φ : E → S → V) (X : E × S → ℝ) : Prop :=
  quadScore μ X (condMean μ φ X) < quadScore μ X (fun _ => expect μ X)

/-- **Delegitimizing**: the reflection equation fails — on some positive-mass verdict value `v`, read as a
forecast of `X`, `E[X 𝟙[V = v]] ≠ v · P(V = v)` (product form).
Source: [[corr-wf14-inventory]] 122 / approval-final.md S11(a) ("*delegitimizing* (breaks the reflection
equation)")
Kind: D
Fidelity: exact (product form) -/
def delegitimizing (μ : Distr (E × S)) (φ : E → S → ℝ) (X : E × S → ℝ) : Prop :=
  ∃ v : ℝ, 0 < ∑ q ∈ univ.filter (fun q : E × S => φ q.1 q.2 = v), μ.mass q ∧
    ∑ q ∈ univ.filter (fun q : E × S => φ q.1 q.2 = v), μ.mass q * X q ≠
      v * ∑ q ∈ univ.filter (fun q : E × S => φ q.1 q.2 = v), μ.mass q

/-! ## N+: one instance of each class on `E = S = Bool`, uniform law -/

/-- The uniform law on `Bool × Bool`. Source: mandate T9. Kind: D. Fidelity: n/a (witness) -/
noncomputable def uniform2 : Distr (Bool × Bool) where
  mass _ := 1 / 4
  nonneg _ := by norm_num
  sum_eq_one := by simp [Fintype.sum_prod_type]

/-- The target `X = 𝟙[E = true]` (the evidence bit). Source: mandate T9. Kind: D. Fidelity: n/a -/
def targetE : Bool × Bool → ℝ := fun p => if p.1 then 1 else 0

/-- **Inert instance**: the verdict `φ e s = s` is a function of `S` alone.
Source: [[corr-wf14-inventory]] 122 / approval-final.md S11(a)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem inert_instance : inert (fun (_ : Bool) (s : Bool) => s) := ⟨id, fun _ _ => rfl⟩

/-- **Legitimizing instance**: the verdict `φ e s = e` reports the evidence; conditioning on it drives the
quadratic score about `𝟙[E = true]` from `1/4` to `0`.
Source: [[corr-wf14-inventory]] 122 / approval-final.md S11(a)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem legitimizing_instance : legitimizing uniform2 (fun (e : Bool) (_ : Bool) => e) targetE := by
  unfold legitimizing quadScore condMean expect targetE uniform2
  simp only [Finset.sum_filter]
  simp [Fintype.sum_prod_type]
  norm_num

/-- **Delegitimizing instance**: the verdict `φ e s = 1/2 + 𝟙[s]/4` (steered by the agent's state) read as a
forecast of `𝟙[E = true]` breaks reflection at `v = 3/4`: `E[X 𝟙[V = 3/4]] = 1/4 ≠ 3/4 · 1/2`.
Source: [[corr-wf14-inventory]] 122 / approval-final.md S11(a)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem delegitimizing_instance :
    delegitimizing uniform2 (fun (_ : Bool) (s : Bool) => if s then (3 / 4 : ℝ) else 1 / 2) targetE := by
  refine ⟨3 / 4, ?_, ?_⟩ <;>
  · simp only [Finset.sum_filter]
    simp [uniform2, targetE, Fintype.sum_prod_type]
    norm_num

/-- The target that is the agent's own state bit, `X = 𝟙[S = true]`.
Source: audit r1 (adversarial N5) probe `LegitimizingOverlap.lean`. Kind: D. Fidelity: n/a (witness) -/
def targetS : Bool × Bool → ℝ := fun p => if p.2 then 1 else 0

/-- **The classes overlap**: on the uniform law with target `𝟙[S = true]`, the verdict `φ e s = s` is
inert (a function of `S`) **and** legitimizing (score `1/4 → 0` against the unconditional mean) — the
unconditional baseline of `legitimizing` does not see that `P_t` already knows `S`. Finding F-22.
Source: audit r1 (adversarial N5) probe `LegitimizingOverlap.lean`; approval-final.md S11(a)
Kind: N+ (overlap witness; a finding about the definitions)
Fidelity: exact
Hyps: (a) only -/
theorem inert_and_legitimizing :
    inert (fun (_ : Bool) (s : Bool) => s) ∧
      legitimizing uniform2 (fun (_ : Bool) (s : Bool) => s) targetS := by
  refine ⟨⟨id, fun _ _ => rfl⟩, ?_⟩
  unfold legitimizing quadScore condMean expect targetS uniform2
  simp only [Finset.sum_filter]
  simp [Fintype.sum_prod_type]
  norm_num

end Legitimizing

end Cleanroom.Corrigibility.CorrLandscape
