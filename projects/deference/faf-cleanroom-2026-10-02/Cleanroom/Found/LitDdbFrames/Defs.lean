import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.BigOperators

/-!
# Deference Done Better: finite probability frames — definitions of record

Package `lit-ddb-frames` (faf-cleanroom run, 2026-09-29). This file is the *definitions module*
(with `Blackwell.lean` and `Local.lean`): every finite-frame deference predicate the run uses is
defined here, over Dorst–Levinstein–Salow–Husic–Fitelson, *Deference Done Better* (DDB).

Carrier and conventions (binding, from the mandate):
* worlds `W : Type` with `[Fintype W] [DecidableEq W]`; distributions are vectors `W → ℝ` in
  `stdSimplex ℝ W`, so `convexHull ℝ` and separation apply to them as points of `W → ℝ`;
* a frame carries `P : W → W → ℝ` (DDB's row-stochastic matrix); the deferrer `π : W → ℝ`
  carries its simplex membership as a hypothesis `hπ : π ∈ stdSimplex ℝ W` in every theorem;
* propositions are `Finset W`; `mass ρ q` is `ρ(q)`; `F.cell ρ` is `[P = ρ]`;
* **no division in a definition of record**: conditioning appears only in product form, guarded by
  positivity of the conditioning event (DDB Appendix B, Lemma 7.1: "this implies
  `π(E(X) ≥ t) > 0`"). The one ratio vector, `Frame.informed` (`P̂`), is meaningful only under
  `0 < F.selfMass ρ`, which every consumer carries (`Frame.ModestlyInformed`, `NewReflects`).

FAF has no probability frames, Blackwell order or finite deference predicates (grep of
`.lake/packages/agentFoundations/` for `Blackwell|garbl`, 2026-09-29: no hits), so nothing here is
a modelling substitution for an FAF object.
-/

namespace Cleanroom.Found.LitDdbFrames

open Finset

noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Frames, expectation, mass -/

/-- A finite probability frame `⟨W, 𝒫⟩`: at each world `w` the expert's distribution `P w` over
`W`, a point of the standard simplex (DDB's row-stochastic matrix, row `w`).
Source: [[Deference Done Better]] §1 ll. 61–63, glossary l. 446 (Probability frame)
Kind: D
Fidelity: exact -/
structure Frame (W : Type) [Fintype W] where
  /-- the expert's probabilities at each world -/
  P : W → W → ℝ
  /-- each row is a probability distribution -/
  P_mem : ∀ w, P w ∈ stdSimplex ℝ W

/-- Expected value `E_ρ(X) = ∑ w, ρ w * X w` of a random variable `X` under `ρ`.
Source: [[Deference Done Better]] §1 l. 115, glossary l. 426
Kind: D
Fidelity: exact -/
def E (ρ X : W → ℝ) : ℝ := ∑ w, ρ w * X w

/-- Probability mass `ρ(q) = ∑ w ∈ q, ρ w` of a proposition `q`.
Source: [[Deference Done Better]] §1 (propositions as subsets of `W`)
Kind: D
Fidelity: exact -/
def mass (ρ : W → ℝ) (q : Finset W) : ℝ := ∑ w ∈ q, ρ w

/-- Indicator variable `𝟙_q` of a proposition.
Source: [[Deference Done Better]] glossary l. 432
Kind: D
Fidelity: exact -/
def ind (q : Finset W) : W → ℝ := fun w => if w ∈ q then 1 else 0

/-- Support `W_ρ = {w : ρ w > 0}` of a distribution (DDB's `W_π`, Definition 7.2.3).
Source: [[Deference Done Better]] glossary l. 464, App. B Def. 7.2.3 l. 508
Kind: D
Fidelity: exact -/
def supp (ρ : W → ℝ) : Finset W := univ.filter (fun w => 0 < ρ w)

/-- The proposition `[P = ρ]`: the worlds at which the expert's distribution is `ρ`.
Source: [[Deference Done Better]] §1 l. 61
Kind: D
Fidelity: exact -/
def Frame.cell (F : Frame W) (ρ : W → ℝ) : Finset W := univ.filter (fun w => F.P w = ρ)

/-- The candidates `C_ρ = {P_w : ρ(P = P_w) > 0}` that `ρ` leaves open — a *set of
distributions* (the image of the support), so several worlds sharing one `P_w` contribute one
candidate (DDB Remark 7.2.1 needs no representatives).
Source: [[Deference Done Better]] glossary l. 412, fn 54
Kind: D
Fidelity: exact -/
def Frame.cands (F : Frame W) (ρ : W → ℝ) : Finset (W → ℝ) := (supp ρ).image F.P

/-- `C_ρ⁻ = C_ρ \ {ρ}`: the candidates `ρ` leaves open other than itself.
Source: [[Deference Done Better]] glossary l. 412, fn 54
Kind: D
Fidelity: exact -/
def Frame.candsMinus (F : Frame W) (ρ : W → ℝ) : Finset (W → ℝ) := (F.cands ρ).erase ρ

/-- The self-cell mass `ρ(P = ρ)`: how much probability `ρ` gives to being the expert.
Source: [[Deference Done Better]] §1 l. 80 (`P_w(P = P_w)`)
Kind: D
Fidelity: exact -/
def Frame.selfMass (F : Frame W) (ρ : W → ℝ) : ℝ := mass ρ (F.cell ρ)

/-- The expert is *modest* at `w` when `P_w(P = P_w) < 1`.
Source: [[Deference Done Better]] §1 l. 61, l. 80
Kind: D
Fidelity: exact -/
def Frame.ModestAt (F : Frame W) (w : W) : Prop := F.selfMass (F.P w) < 1

/-- An *immodest* frame: `P_w(P = P_w) = 1` at every world.
Source: [[Deference Done Better]] §1 l. 82, l. 89
Kind: D
Fidelity: exact -/
def Frame.Immodest (F : Frame W) : Prop := ∀ w, F.selfMass (F.P w) = 1

/-- The *informed expert* `P̂_ρ = ρ(· | P = ρ)`, as the ratio vector
`w ↦ 𝟙[P_w = ρ] · ρ w / ρ(P = ρ)`. It is DDB's object only when `0 < F.selfMass ρ`; at a null
self-cell Lean's `x / 0 = 0` makes it the zero vector, and every consumer of this definition
(`Frame.ModestlyInformed`, `NewReflects`) carries that positivity, so the junk value never enters
a headline.
Source: [[Deference Done Better]] §1 l. 95, glossary l. 434
Kind: D
Fidelity: exact (under `0 < selfMass ρ`; see docstring) -/
def Frame.informed (F : Frame W) (ρ : W → ℝ) : W → ℝ :=
  fun w => if F.P w = ρ then ρ w / F.selfMass ρ else 0

/-! ## Reflection principles (product form, guarded by candidacy) -/

/-- **Reflection**: `π(· | P = ρ) = ρ` for every candidate `ρ ∈ C_π`, in product form
`π w · 𝟙[P_w = ρ] = π(P = ρ) · ρ w`. Candidacy is the positivity guard `π(P = ρ) > 0` (DDB's
conditional probabilities are defined only on positive-probability events).
Source: [[Deference Done Better]] §1 l. 75, glossary l. 450
Kind: D
Fidelity: exact -/
def Reflects (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ ρ ∈ F.cands π, ∀ w, π w * ind (F.cell ρ) w = mass π (F.cell ρ) * ρ w

/-- **New Reflection** (strong reading, NR-str): for every candidate `ρ ∈ C_π` the informed
expert exists (`0 < ρ(P = ρ)`) and `π(· | P = ρ) = ρ(· | P = ρ)` in product form,
`π w · 𝟙[P_w = ρ] · ρ(P = ρ) = π(P = ρ) · ρ w · 𝟙[P_w = ρ]`. This is the reading DDB's informed
version (fn 12) and fn 19's bet presuppose. `lit-ddb-facts` chooses between this and
`NewReflectsVac` for items 039/042; under Total Trust they coincide (`TotalTrust.lean`).
Source: [[Deference Done Better]] §1 l. 86, l. 97, fn 12, glossary l. 438
Kind: D
Fidelity: exact (strong reading; the vacuous reading is `NewReflectsVac`) -/
def NewReflects (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ ρ ∈ F.cands π, 0 < F.selfMass ρ ∧
    ∀ w, π w * ind (F.cell ρ) w * F.selfMass ρ = mass π (F.cell ρ) * ρ w * ind (F.cell ρ) w

/-- **New Reflection** (vacuous reading, NR-vac): the clause at a candidate `ρ` is required only
when the informed expert exists (`0 < ρ(P = ρ)`); at a null self-cell it is vacuous.
Source: [[Deference Done Better]] §1 l. 86 (reading), glossary l. 438
Kind: D
Fidelity: variant: weaker reading than `NewReflects`, see its docstring -/
def NewReflectsVac (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ ρ ∈ F.cands π, 0 < F.selfMass ρ →
    ∀ w, π w * ind (F.cell ρ) w * F.selfMass ρ = mass π (F.cell ρ) * ρ w * ind (F.cell ρ) w

/-- The strong reading of New Reflection implies the vacuous one.
Source: none: infrastructure (Target 1)
Kind: L
Fidelity: n/a -/
theorem NewReflects.vac {π : W → ℝ} {F : Frame W} (h : NewReflects π F) : NewReflectsVac π F :=
  fun ρ hρ _ => (h ρ hρ).2

/-! ## Trust principles (product form) -/

/-- The proposition `[P(q) ≥ t]`: worlds where the expert's probability of `q` is at least `t`.
Source: [[Deference Done Better]] §2 l. 145
Kind: D
Fidelity: exact -/
def Frame.probEvent (F : Frame W) (q : Finset W) (t : ℝ) : Finset W :=
  univ.filter (fun w => t ≤ mass (F.P w) q)

/-- **Simple Trust**: `π(q | P(q) ≥ t) ≥ t` for all `q, t`, in product form
`t · π(P(q) ≥ t) ≤ π(q ∧ P(q) ≥ t)`, guarded by `0 < π(P(q) ≥ t)`; thresholds range over all of
`ℝ` (the reduction to attained thresholds is a lemma, not part of the definition).
Source: [[Deference Done Better]] §2 l. 145, glossary l. 452
Kind: D
Fidelity: exact -/
def SimpleTrust (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ (q : Finset W) (t : ℝ), 0 < mass π (F.probEvent q t) →
    t * mass π (F.probEvent q t) ≤ mass π (q ∩ F.probEvent q t)

/-- The proposition `[P(q | p) ≥ t]`, product-guarded: worlds where `P_w(p) > 0` and
`t · P_w(p) ≤ P_w(q ∧ p)`. A world where `P_w(p) = 0` has no conditional probability and is
excluded (DDB's convention).
Source: [[Deference Done Better]] §2 l. 154
Kind: D
Fidelity: exact -/
def Frame.condProbEvent (F : Frame W) (q p : Finset W) (t : ℝ) : Finset W :=
  univ.filter (fun w => 0 < mass (F.P w) p ∧ t * mass (F.P w) p ≤ mass (F.P w) (q ∩ p))

/-- **Trust**: `π(q | p ∧ [P(q | p) ≥ t]) ≥ t` for all `q, p, t`, in product form, guarded by
positivity of the conditioning event.
Source: [[Deference Done Better]] §2 l. 154, glossary l. 458
Kind: D
Fidelity: exact -/
def Trust (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ (q p : Finset W) (t : ℝ), 0 < mass π (p ∩ F.condProbEvent q p t) →
    t * mass π (p ∩ F.condProbEvent q p t) ≤ mass π (q ∩ (p ∩ F.condProbEvent q p t))

/-- **Total Trust**, the definition of record in denominator-free product form:
`∀ X s, 0 ≤ ∑ w, π w · (X w − s) · 𝟙[s ≤ E_{P_w}(X)]`. Off `π`-null events this is exactly DDB's
`E_π(X | E(X) ≥ s) ≥ s` (`TotalTrust.lean`, `totalTrust_iff_cond`), and on a `π`-null event the
product inequality holds trivially, which is DDB's convention. Thresholds `s` range over all of
`ℝ` and `X` over all random variables: quantifying over attained thresholds or indicator
variables only is a strictly weaker predicate. Every finite-frame Total Trust in the run is this
declaration; `def-lattice` states the same shape over FAF LUVs.
Source: [[Deference Done Better]] §2 l. 175, glossary l. 456; rigor critique 11
Kind: D
Fidelity: exact -/
def TotalTrust (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ (X : W → ℝ) (s : ℝ), 0 ≤ ∑ w, π w * (X w - s) * (if s ≤ E (F.P w) X then 1 else 0)

/-- A frame *validates* a deference principle `Φ` when every candidate `P_i` defers `Φ`-wise to
the frame.
Source: [[Deference Done Better]] §4 l. 337, glossary l. 460
Kind: D
Fidelity: exact -/
def Frame.Validates (F : Frame W) (Φ : (W → ℝ) → Frame W → Prop) : Prop := ∀ i, Φ (F.P i) F

/-! ## Decision problems, strategies, Value -/

/-- A decision problem: a finite set of options (random variables). Both `Value` and `WeakValue`
quantify over *nonempty* problems — the empty menu has no strategy.
Source: [[Deference Done Better]] §1 l. 113, glossary l. 420
Kind: D
Fidelity: exact -/
abbrev DecisionProblem (W : Type) := Finset (W → ℝ)

/-- A *strategy* for `𝒪` on the frame: `S w ∈ 𝒪` at every world, with the **cell constraint**
`P_w = P_v → S w = S v` (a strategy chooses by the expert's probabilities, not by the world).
The constraint is load-bearing: without it Theorem 2.2 is false (`Examples.lean`, Target 23).
Source: [[Deference Done Better]] §1 l. 117, glossary l. 454
Kind: D
Fidelity: exact -/
def Frame.IsStrategy (F : Frame W) (𝒪 : DecisionProblem W) (S : W → (W → ℝ)) : Prop :=
  (∀ w, S w ∈ 𝒪) ∧ ∀ w v, F.P w = F.P v → S w = S v

/-- A strategy is *recommended* by the frame for `𝒪` when it is a strategy and at every world
its choice maximises expected utility under the expert's probabilities there.
Source: [[Deference Done Better]] §1 l. 117, glossary l. 454
Kind: D
Fidelity: exact -/
def Frame.Recommended (F : Frame W) (𝒪 : DecisionProblem W) (S : W → (W → ℝ)) : Prop :=
  F.IsStrategy 𝒪 S ∧ ∀ w, ∀ o ∈ 𝒪, E (F.P w) o ≤ E (F.P w) (S w)

/-- `E_π(S) = ∑ w, π w · S_w(w)`: the expected utility of following a strategy.
Source: [[Deference Done Better]] §1 l. 117, glossary l. 426
Kind: D
Fidelity: exact -/
def stratValue (π : W → ℝ) (S : W → (W → ℝ)) : ℝ := ∑ w, π w * S w w

/-- **Value**: for every nonempty decision problem and *every* recommended strategy `S`,
`E_π(S) ≥ E_π(O)` for every option `O`.
Source: [[Deference Done Better]] §1 l. 121, glossary l. 462
Kind: D
Fidelity: exact -/
def Value (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ 𝒪 : DecisionProblem W, 𝒪.Nonempty →
    ∀ S, F.Recommended 𝒪 S → ∀ o ∈ 𝒪, E π o ≤ stratValue π S

/-- **Weak Value**: for every nonempty decision problem *some* recommended strategy `S` has
`E_π(S) ≥ E_π(O)` for every option `O`.
Source: [[Deference Done Better]] App. B l. 472
Kind: D
Fidelity: exact -/
def WeakValue (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ 𝒪 : DecisionProblem W, 𝒪.Nonempty →
    ∃ S, F.Recommended 𝒪 S ∧ ∀ o ∈ 𝒪, E π o ≤ stratValue π S

/-- The two-option witness strategy for the menu `{X, const s}`: take `X` exactly where the
expert's estimate of `X` is at least `s`. Its value identity is the product form of Total Trust
(`TotalTrust.lean`, `stratValue_twoOption`).
Source: [[Deference Done Better]] §2 l. 190 (proof sketch of 2.2, ⇐), App. B Lemma 7.1
Kind: D
Fidelity: exact -/
def Frame.twoOption (F : Frame W) (X : W → ℝ) (s : ℝ) : W → (W → ℝ) :=
  fun w => if s ≤ E (F.P w) X then X else fun _ => s

/-! ## Modest informedness, class-convexity, the hull condition -/

/-- A candidate `ρ` is **modestly informed**: its informed self exists (`0 < ρ(P = ρ)`) and `ρ`
lies in the convex hull of `{P̂_ρ} ∪ C_ρ⁻`. No positivity of the self-weight is built in — that is
Lemma 7.4's *conclusion* (`Cycle.lean`). Stated on distributions, so duplicate rows (Remark
7.2.1) need no representatives; `Frame.ModestlyInformedAt` is the index-by-world form.
Source: [[Deference Done Better]] §4 l. 325, fn 54, glossary l. 436
Kind: D
Fidelity: exact -/
def Frame.ModestlyInformed (F : Frame W) (ρ : W → ℝ) : Prop :=
  0 < F.selfMass ρ ∧ ρ ∈ convexHull ℝ (insert (F.informed ρ) (↑(F.candsMinus ρ) : Set (W → ℝ)))

/-- `P_i` is modestly informed, indexed by a world `i`.
Source: [[Deference Done Better]] §4 l. 325
Kind: D
Fidelity: exact -/
abbrev Frame.ModestlyInformedAt (F : Frame W) (i : W) : Prop := F.ModestlyInformed (F.P i)

/-- **Class-convexity** of `W_π` (Definition 7.2.6): every candidate `ρ ∈ C_π` lies in the convex
hull of its informed self and the *other candidates of `π`* (rather than the other candidates `ρ`
itself leaves open). Stated without a positivity guard, as in DDB; under `π ∈ convexHull C_π`
it implies `0 < ρ(P = ρ)` (`Hull.lean`).
Source: [[Deference Done Better]] App. B Def. 7.2.6 l. 522
Kind: D
Fidelity: exact -/
def ClassConvex (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ ρ ∈ F.cands π, ρ ∈ convexHull ℝ (insert (F.informed ρ) (↑((F.cands π).erase ρ) : Set (W → ℝ)))

/-- The fourth condition of Theorem 7.6: `π` lies in the convex hull of its candidates and every
candidate is modestly informed.
Source: [[Deference Done Better]] §4 l. 327 (Theorem 4.1), App. B l. 630
Kind: D
Fidelity: exact -/
def HullAndModestlyInformed (π : W → ℝ) (F : Frame W) : Prop :=
  π ∈ convexHull ℝ (↑(F.cands π) : Set (W → ℝ)) ∧ ∀ ρ ∈ F.cands π, F.ModestlyInformed ρ

end

end Cleanroom.Found.LitDdbFrames
