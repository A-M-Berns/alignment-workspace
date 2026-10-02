import Cleanroom.Found.LitDdbFrames

/-!
# DDB's accuracy theorems — definitions of record

Package `lit-ddb-accuracy-mm` (faf-cleanroom run, 2026-09-29/30). Targets 1–3 of the mandate:
per-variable Total Trust, estimate-inaccuracy rules and the classes (gsp, value-directed,
monotone strictly proper, Levinstein's local class), Epistemic Value with respect to a variable,
and the explicit rule families (`clamp`, `mixRule`, `ruleC`, `brier`, `stepRule`).

Conventions (binding, from the mandate): worlds `W` finite; distributions in `stdSimplex ℝ W`;
frames `Frame W` from the foundation; the deferrer `π` with `hπ : π ∈ stdSimplex ℝ W`. Rules are
**value-indexed**: `I x k` is the inaccuracy of estimate `x` when the true value is `k`; DDB's
world-indexed `I_X(x, w)` is `I x (X w)`. No division in a definition of record; every "for all
`t`" ranges over `ℝ`.

FAF has no scoring rules (grep of `.lake/packages/agentFoundations/` for
`scoring|proper|Schervish|Blackwell`, mandate 2026-09-29: no hits), so nothing here stands in for
an FAF object.
-/

namespace Cleanroom.Lit.LitDdbAccuracyMm

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Target 1: per-variable Total Trust -/

/-- **Total Trust with respect to `X`** (DDB §3: "`π` totally trusts `P` with respect to `X` iff
for all `t`: `E_π(X | E(X) ≥ t) ≥ t` and `E_π(X | E(X) ≤ t) ≤ t`"), in denominator-free product
form: clause 1 is `0 ≤ ∑ w, π w · (X w − s) · 𝟙[s ≤ E_{P_w}(X)]`, clause 2 is
`∑ w, π w · (X w − s) · 𝟙[E_{P_w}(X) ≤ s] ≤ 0`, both for every real `s`. Both clauses are needed
for a single `X`: the dual trick `X ↦ −X` swaps them across variables, not within one. These two
clauses are literally Lemma 7.10 (1)–(2) (whose `t ∈ [0, 1]` is a typo for `t ∈ ℝ`).
`TotalTrust π F ↔ ∀ X, TotalTrustOn X π F` is `totalTrust_iff_forall_totalTrustOn`.
Source: [[Deference Done Better]] §3 l. 271, App. B Lemma 7.10 l. 774
Kind: D
Fidelity: exact -/
def TotalTrustOn (X : W → ℝ) (π : W → ℝ) (F : Frame W) : Prop :=
  (∀ s : ℝ, 0 ≤ ∑ w, π w * (X w - s) * (if s ≤ E (F.P w) X then 1 else 0)) ∧
  (∀ s : ℝ, ∑ w, π w * (X w - s) * (if E (F.P w) X ≤ s then 1 else 0) ≤ 0)

/-! ## Target 2: rules and the classes -/

/-- An **estimate-inaccuracy rule**, value-indexed: `I x k` is the inaccuracy of the estimate `x`
when the true value of the variable is `k`. DDB write `I_X(e, w)` with a world argument; every
rule in the paper (fn 46, fn 67, the six-case rule, Brier `(k − x)^2`) depends on `w` only
through `X w`, and Campbell-Moore's and Theorem 7.9's form is value-indexed, so `I_X(e, w)` is
`I e (X w)` here (`variant` noted once, here).
Source: [[Deference Done Better]] §3 l. 267, glossary l. 424
Kind: D
Fidelity: variant: value-indexed (`I x (X w)` for DDB's `I_X(x, w)`) -/
abbrev Rule := ℝ → ℝ → ℝ

/-- `E_ρ(I_X(x))`: the expected inaccuracy under `ρ` of the fixed estimate `x` of `X`.
Source: [[Deference Done Better]] glossary l. 424 (`I_X(e)` as a random variable)
Kind: D
Fidelity: exact -/
def expInacc (ρ X : W → ℝ) (I : Rule) (x : ℝ) : ℝ := ∑ w, ρ w * I x (X w)

/-- `E_π(I_X(P))`: the expected inaccuracy of the expert's estimate of `X`, whatever it is
(`I_X(P)(w) = I_X(E_w(X), w)`).
Source: [[Deference Done Better]] §3 l. 269, glossary l. 424
Kind: D
Fidelity: exact -/
def expInaccP (π : W → ℝ) (F : Frame W) (X : W → ℝ) (I : Rule) : ℝ :=
  ∑ w, π w * I (E (F.P w) X) (X w)

/-- **Generally strictly proper (gsp)**, DDB fn 47 verbatim: every probability function on the
frame's worlds expects its own estimate of `X` to be strictly less inaccurate than any other
estimate: `∀ ρ, ∀ s ≠ E_ρ(X), E_ρ(I_X(ρ)) < E_ρ(I_X(s))`. Quantified over all real `s`.
Source: [[Deference Done Better]] §3 l. 267, fn 47
Kind: D
Fidelity: exact -/
def IsGsp (X : W → ℝ) (I : Rule) : Prop :=
  ∀ ρ ∈ stdSimplex ℝ W, ∀ s : ℝ, s ≠ E ρ X → expInacc ρ X I (E ρ X) < expInacc ρ X I s

/-- **Gsp on the value range**: fn 47 required only for estimates `s` in `[min X, max X]`
(`∃ w, X w ≤ s` and `∃ w, s ≤ X w`). Theorem 3.2's proofs use the rule only at such estimates,
and Levinstein's strictly proper local rules (estimates in `[0, 1]`, Theorem 3.1) are literally
`IsGspOn (ind q)` (`strictlyProperLocal_iff_isGspOn`). `IsGsp X I → IsGspOn X I` is
`IsGsp.isGspOn`.
Source: [[Deference Done Better]] fn 47 (restricted to the value range); mandate Target 2
Kind: D
Fidelity: variant: weaker than `IsGsp` (estimates restricted to `[min X, max X]`) -/
def IsGspOn (X : W → ℝ) (I : Rule) : Prop :=
  ∀ ρ ∈ stdSimplex ℝ W, ∀ s : ℝ, (∃ w, X w ≤ s) → (∃ w, s ≤ X w) → s ≠ E ρ X →
    expInacc ρ X I (E ρ X) < expInacc ρ X I s

/-- **Value-directed** (Campbell-Moore 2020, quoted at DDB l. 650): moving an estimate toward the
true value strictly reduces inaccuracy — if `e₁ < e₂ ≤ X w` or `X w ≤ e₂ < e₁` then
`I e₂ (X w) < I e₁ (X w)`.
Source: [[Deference Done Better]] App. B §7.3.1 l. 650
Kind: D
Fidelity: exact -/
def ValueDirected (X : W → ℝ) (I : Rule) : Prop :=
  ∀ w, ∀ e₁ e₂ : ℝ, (e₁ < e₂ ∧ e₂ ≤ X w → I e₂ (X w) < I e₁ (X w)) ∧
    (X w ≤ e₂ ∧ e₂ < e₁ → I e₂ (X w) < I e₁ (X w))

/-- **Value-directed on the value range**: l. 650's two clauses asked only of estimates in
`[min X, max X]` — clause 1 for `min X ≤ e₁ < e₂ ≤ X w`, clause 2 for `X w ≤ e₂ < e₁ ≤ max X`,
the range bounds as existentials (`∃ w₀, X w₀ ≤ e₁`, `∃ w₀, e₁ ≤ X w₀`) like `IsGspOn`. This is
the reading on which Campbell-Moore's "every gsp estimate-inaccuracy measure is value-directed"
is true, and it is **derived** from `IsGspOn` here (`IsGspOn.valueDirectedOn`, `Monotone.lean`);
off the range gsp constrains nothing pointwise and the implication is false (audit r1 probes
`plateauRule`, `bumpRule`; findings F9). `ValueDirected X I → ValueDirectedOn X I` is
`ValueDirected.valueDirectedOn`.
Source: [[Deference Done Better]] App. B §7.3.1 l. 650, on Theorem 7.9's domain
`[v₀, vₙ] × [v₀, vₙ]` (l. 766); audit r1 (fidelity B1, adversarial B1)
Kind: D
Fidelity: variant: l. 650 restricted to the value range -/
def ValueDirectedOn (X : W → ℝ) (I : Rule) : Prop :=
  ∀ w, ∀ e₁ e₂ : ℝ,
    ((∃ w₀, X w₀ ≤ e₁) → e₁ < e₂ → e₂ ≤ X w → I e₂ (X w) < I e₁ (X w)) ∧
    ((∃ w₀, e₁ ≤ X w₀) → X w ≤ e₂ → e₂ < e₁ → I e₂ (X w) < I e₁ (X w))

/-- **Monotone strict propriety** (DDB l. 654): for every probability function `ρ` with
`e := E_ρ(X)`, estimates strictly further from `e` on the same side are expected to be strictly
more inaccurate: `e ≤ s < t ≤ max X → E_ρ(I_X(s)) < E_ρ(I_X(t))` and
`min X ≤ s < t ≤ e → E_ρ(I_X(t)) < E_ρ(I_X(s))`. The range bounds are `∃ w, t ≤ X w` and
`∃ w, X w ≤ s`.
Source: [[Deference Done Better]] App. B §7.3.1 l. 654
Kind: D
Fidelity: exact -/
def MonotoneStrictlyProper (X : W → ℝ) (I : Rule) : Prop :=
  ∀ ρ ∈ stdSimplex ℝ W, ∀ s t : ℝ, s < t →
    (E ρ X ≤ s → (∃ w, t ≤ X w) → expInacc ρ X I s < expInacc ρ X I t) ∧
    (t ≤ E ρ X → (∃ w, X w ≤ s) → expInacc ρ X I t < expInacc ρ X I s)

/-- The event `[E(X) = e]`: worlds where the expert's estimate of `X` equals `e`.
Source: [[Deference Done Better]] §3 l. 273 (the equality clause of Theorem 3.2)
Kind: D
Fidelity: exact -/
def estEq (F : Frame W) (X : W → ℝ) (e : ℝ) : Finset W :=
  univ.filter (fun w => E (F.P w) X = e)

/-- **Epistemic Value with respect to `X`**, fn 48 verbatim: for every gsp rule `I` (fn 47, all
real estimates), `E_π(I_X(P)) ≤ E_π(I_X(π))`, with equality iff `π(E(X) = E_π(X)) = 1`. The
class is gsp alone: the value-directedness that Theorem 3.2's (⟹) proof uses (on the value
range only) is derived from gsp (`IsGspOn.valueDirectedOn`), not assumed — the audit-r1 repair.
The earlier class `gsp ∧ value-directed on all of ℝ` was a proper subclass, and the citation of
Campbell-Moore 2020 could not close the gap (findings F9). Nothing in the package *assumes*
value-directedness of a rule it builds — for `mixRule`/`stepRule` it is proved. The equality
clause is the glossary's "iff" (l. 424; fn 48 prints "only if").
Source: [[Deference Done Better]] §3 l. 269, fn 47, fn 48, glossary l. 424 (Epistemic Value)
Kind: D
Fidelity: exact (class: gsp, fn 47; value-indexed rules as `Rule` discloses) -/
def EpistemicValueOn (X : W → ℝ) (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ I : Rule, IsGsp X I →
    expInaccP π F X I ≤ expInacc π X I (E π X) ∧
    (expInaccP π F X I = expInacc π X I (E π X) ↔ mass π (estEq F X (E π X)) = 1)

/-! ### Levinstein's class (Theorem 3.1) -/

/-- The proposition `[P(q) ≤ t]` (the below-threshold event of Simple Trust with respect to `q`).
Source: [[Deference Done Better]] §3 l. 255
Kind: D
Fidelity: exact -/
def probEventLE (F : Frame W) (q : Finset W) (t : ℝ) : Finset W :=
  univ.filter (fun w => mass (F.P w) q ≤ t)

/-- **Simple Trust with respect to `q`** (DDB §3 l. 255): `π(q | P(q) ≥ t) ≥ t` and
`π(q | P(q) ≤ t) ≤ t` for all real `t`, in product form
`t · π(P(q) ≥ t) ≤ π(q ∧ P(q) ≥ t)` and `π(q ∧ P(q) ≤ t) ≤ t · π(P(q) ≤ t)`. On a `π`-null event
both sides vanish, so no positivity guard is needed; it is `TotalTrustOn (ind q)`
(`simpleTrustOn_iff_totalTrustOn_ind`).
Source: [[Deference Done Better]] §3 l. 255
Kind: D
Fidelity: exact -/
def SimpleTrustOn (q : Finset W) (π : W → ℝ) (F : Frame W) : Prop :=
  (∀ t : ℝ, t * mass π (F.probEvent q t) ≤ mass π (q ∩ F.probEvent q t)) ∧
  (∀ t : ℝ, mass π (q ∩ probEventLE F q t) ≤ t * mass π (probEventLE F q t))

/-- **Truth-directed** local rule for `q` (fn 42: "if `|δ(q) − i| < |ρ(q) − i|` then
`I_q(δ, i) < I_q(ρ, i)` for `i = 0, 1`", quantified over probability functions, so over estimates
in `[0, 1]`): value-directedness at the indicator `𝟙_q` on its value range, `ValueDirectedOn
(ind q)`. A local rule `I_q(δ, i)` is `I (δ q) i` here, so a local rule is a `Rule` used at
`X = ind q`. For `∅ ≠ q ≠ univ` the range is `[0, 1]` and both truth values occur, so this is
fn 42 exactly; for trivial `q` the range is a point and the predicate is vacuous where fn 42
still constrains the unrealised truth value (weaker there; immaterial for Theorem 3.1, whose two
directions hold for every class between the witness's and the strictly proper local rules,
`simpleTrustOn_iff_forall_strictlyProperLocal`). (Audit r1 N2: the earlier `ValueDirected (ind q)`
constrained estimates outside `[0, 1]`, which fn 42 does not.)
Source: [[Deference Done Better]] §3 l. 249, fn 42
Kind: D
Fidelity: exact for `∅ ≠ q ≠ univ`; weaker (vacuous) for trivial `q` -/
abbrev TruthDirected (q : Finset W) (I : Rule) : Prop := ValueDirectedOn (ind q) I

/-- **Strictly proper** local rule for `q` (fn 43, weak form with the equality clause): for all
probability functions `δ, ρ`, `E_δ(I_q(δ)) ≤ E_δ(I_q(ρ))` with equality iff `δ(q) = ρ(q)`.
Source: [[Deference Done Better]] §3 l. 249, fn 43
Kind: D
Fidelity: exact -/
def StrictlyProperLocal (q : Finset W) (I : Rule) : Prop :=
  ∀ δ ∈ stdSimplex ℝ W, ∀ ρ ∈ stdSimplex ℝ W,
    expInacc δ (ind q) I (mass δ q) ≤ expInacc δ (ind q) I (mass ρ q) ∧
    (expInacc δ (ind q) I (mass δ q) = expInacc δ (ind q) I (mass ρ q) ↔ mass δ q = mass ρ q)

/-! ## Target 3: the explicit rule families -/

/-- `clamp α β x = max α (min β x)`: the projection of `x` onto `[α, β]`.
Source: none: infrastructure (mandate Target 3)
Kind: D
Fidelity: n/a -/
def clamp (α β x : ℝ) : ℝ := max α (min β x)

/-- The **one-piece clamp term** `Λ_{α,β}(x, k) := (clamp x − k)^2 − (clamp k − k)^2`, the closed
form of `2 ∫_k^x (t − k) 𝟙_{[α,β]}(t) dt` (weight `2` on `[α, β]`, `0` elsewhere).
Source: [[Deference Done Better]] fn 67 (`λ(dt) = 2C dt` on `[α, β]`), mandate Target 3
Kind: D
Fidelity: n/a -/
def clampTerm (α β x k : ℝ) : ℝ := (clamp α β x - k) ^ 2 - (clamp α β k - k) ^ 2

/-- The **mixed rule** `c · (x − k)^2 + d · Λ_{α,β}(x, k)`: Brier with weight `c` plus the clamp
term with weight `d`; the closed form of `2∫_k^x (t − k) h(t) dt` for the step density
`h = c + d·𝟙_{[α,β]}`. It is gsp and value-directed for `0 < c`, `0 ≤ d` (`Witness.lean`).
Source: [[Deference Done Better]] fn 67, fn 46; mandate Target 3
Kind: D
Fidelity: n/a -/
def mixRule (α β c d : ℝ) : Rule := fun x k => c * (x - k) ^ 2 + d * clampTerm α β x k

/-- DDB's **six-case rule** in closed form: `(x − k)^2 + (C − 1)·Λ_{α,β}(x, k)` — the rule of
fn 67 with `λ(dt) = 2 dt` everywhere except `[α, β]`, where it is `2C dt`. (The six cases of
l. 720 are the cases of `clamp` for `x, k` relative to `[α, β]`.)
Source: [[Deference Done Better]] App. B l. 720, fn 67; mandate Target 3
Kind: D
Fidelity: exact (closed form of the printed six-case rule) -/
def ruleC (α β C : ℝ) : Rule := mixRule α β 1 (C - 1)

/-- The **Brier rule** for estimates, `(x − k)^2`.
Source: [[Deference Done Better]] App. B l. 770
Kind: D
Fidelity: exact -/
def brier : Rule := fun x k => (x - k) ^ 2

/-- The **step class**: `c · (x − k)^2 + ∑ i, d i · Λ_{a i, b i}(x, k)` over `n` pieces — the
closed form of `2∫_k^x (t − k) h(t) dt` for the step density `h = c + ∑ i, d i · 𝟙_{[a i, b i]}`.
With `0 < c` and all `d i ≥ 0` the density is a positive step function bounded below by `c`;
`mixRule` is the one-piece case (`mixRule_eq_stepRule`) and `ruleC` the case `c = 1`. (A step
density with a piece below the outside level, like fn 46's, is written with `c` the minimum level
and nonnegative increments.)
Source: [[Deference Done Better]] App. B Theorem 7.9 (step densities); mandate Target 3
Kind: D
Fidelity: n/a -/
def stepRule (c : ℝ) {n : ℕ} (a b d : Fin n → ℝ) : Rule :=
  fun x k => c * (x - k) ^ 2 + ∑ i, d i * clampTerm (a i) (b i) x k

/-- **Fn 46's rule**: density `1` on `[−1/10, 1/10]` and `1/1000` outside, i.e.
`I x k = ∫_k^x (t − k) f(t) dt` with `f = 1/1000 + (999/1000)·𝟙_{[−1/10,1/10]}` — in closed form
`mixRule (−1/10) (1/10) (1/2000) (999/2000)` (the factor `1/2` because `mixRule` integrates
`2(t − k) h`).
Source: [[Deference Done Better]] fn 46
Kind: D
Fidelity: exact -/
def fn46Rule : Rule := mixRule (-1 / 10) (1 / 10) (1 / 2000) (999 / 2000)

end

end Cleanroom.Lit.LitDdbAccuracyMm
