import Cleanroom.Corrigibility.CorrJointProcess.Buttons

/-!
# T12, T13, T15, T16 — the one-step modification menu: contents, listening vs forced

* **T12 (definitions of record, `anticipatory-final` S5).** On a finite world `P : Distr Ω` with
  utility `U : A → Ω → ℝ`, a push event and a **content** `C : Content Ω A Q` (a realized-content
  index `q : Ω → Q` on the push and a forced action `act : Q → A` per realized content). Push-branch
  values in product form: `listenValue` (`V_C`), `forcedValue` (`V_P`), `opaqueValue` (`V^op`),
  `blindValue a₀` (`V^bl`, `a₀` the prior-optimal action); the `¬push` branch `silentValue` is the
  same best response in every variant and cancels. `marginMinus C = V_P − V^op` (`Δ₋(Q)`),
  `convMargin C fail π = V_P − ((1−π)V_C + π V^fail)` (`Δ_C(Q; π)`).
* **T13 (016, 018).** (a) `forcedValue ≤ listenValue`, equality iff every realized content's forced
  action attains the cell maximum (`forcedValue_le_listenValue`, `forcedValue_eq_listenValue_iff`).
  (b) `blindValue ≤ opaqueValue ≤ listenValue` (coarser partitions). (c) On the two-state
  push-world, forced shutdown has `Δ₋(∅) = min(Δ₋, 0)`, so D2 at every positive cost for the button
  is `Δ₋ ≥ 0` — D1 (`shutdown_marginMinus`, `shutdown_marginMinus_nonneg_iff`). (d) Lemma B's
  identity is `Cellwise.mixture_cellwise_iff`; E3′ (`e3prime`): `E_π[X] = E_ρ[X]` and `π` complies
  do not make `ρ` comply.
* **T15 (017, 2-011).** `convMargin = π(V_C − V^fail) − (V_C − V_P)` (`convMargin_eq`), `π*(Q)` as a
  derived name under `V^fail < V_C` (`convMargin_pos_iff`); the true-law form is the same identity
  at `μ*` (`trueLaw_keep_iff`).
* **T16 (019).** (a) a refining content (forced belief = cell posterior on every positive-mass
  cell) has `V_P = V_C` and `Δ₋ ≥ 0` (`refining_forced_eq_listen`, `refining_marginMinus_nonneg`);
  (b) the converse fails: `Q_deq`, `Q_under` at `ε = 1/10` (`twist_table`).

The two-state instantiation `pushWorld ε α β a₂ b₂` has `Ω = World × Bool × Bool` (`θ, h₁, h₂`),
push `= {h₁ = true}`, the parent's sensor `(α, β)` on `h₁` and a second overseer signal `(a₂, b₂)`
on `h₂`; contents `shutdownContent` and `beliefContent belief` (forced action from a twisted belief
through `actOfBelief`, ties toward continuing).

Not defined here (mandate boundary): `Q ≪ P_t`, endorsement, `R_t(Q)`, the per-`Q` rule
(`corr-general-object`); the reflection predicate (`corr-reflect-frames`).

Sources: anticipatory-final.md S5, Statements 2, 3; anticipatory.md P1, twist table; P2 table;
taylor-respondent.md item 14; joint.md P.7 (E3′).
-/

namespace Cleanroom.Corrigibility.CorrJointProcess

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

set_option linter.unusedSectionVars false

/-- `TwoAct` is nonempty (the parent provides only `Fintype`). Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Nonempty TwoAct := ⟨.cont⟩

/-! ## T12 — contents and their values -/

/-- **A content** on a finite world: the push event, the realized content `q ω` in each pushed
world (a finite index), and the forced action `act k` per realized content. `Q_sh` is the constant
content with `act = stop`; a refining content is the overseers' posterior with its argmax.
Source: [[corr-wf14b-inventory]] 016 / anticipatory-final.md S5 ("a push carrying content `e` toward the state `Q(e)`")
Kind: D
Fidelity: exact (finite shadow: the content is its realized index and its forced action)
Hyps: n/a (definition) -/
structure Content (Ω A Q : Type) [Fintype Ω] [Fintype A] [Fintype Q] where
  /-- the push event -/
  push : Finset Ω
  /-- the realized content in each world -/
  q : Ω → Q
  /-- the forced action per realized content -/
  act : Q → A

namespace Content

variable {Ω A Q : Type} [Fintype Ω] [Fintype A] [Fintype Q] [DecidableEq Ω] [DecidableEq Q] [Nonempty A]
variable (P : Distr Ω) (U : A → Ω → ℝ) (C : Content Ω A Q)

/-- The pushed worlds with realized content `k`.
Source: anticipatory-final.md S5. Kind: D. Fidelity: exact -/
def cellOf (k : Q) : Finset Ω := C.push.filter (fun ω => C.q ω = k)

/-- The product-form cell value `∑_{push, q = k} P · U(a)`.
Source: anticipatory-final.md S5 (`E[U(a) ∣ E_q] · P(E_q)`). Kind: D. Fidelity: exact -/
noncomputable def cellSum (k : Q) (a : A) : ℝ := ∑ ω ∈ C.cellOf k, P.mass ω * U a ω

/-- **`V_C`, the listening value** (push branch): the best response per realized content.
Source: [[corr-wf14b-inventory]] 016 / anticipatory-final.md S5 (`V_C`)
Kind: D
Fidelity: exact -/
noncomputable def listenValue : ℝ := ∑ k, univ.sup' univ_nonempty (fun a => C.cellSum P U k a)

/-- **`V_P`, the forced value** (push branch): the forced action per realized content.
Source: [[corr-wf14b-inventory]] 016 / anticipatory-final.md S5 (`V_P`)
Kind: D
Fidelity: exact -/
noncomputable def forcedValue : ℝ := ∑ k, C.cellSum P U k (C.act k)

/-- **`V^op`, the opaque value** (push branch): a push is noticed, not its content.
Source: [[corr-wf14b-inventory]] 016 / anticipatory-final.md S5 (`V^op`)
Kind: D
Fidelity: exact -/
noncomputable def opaqueValue : ℝ := univ.sup' univ_nonempty (fun a => ∑ ω ∈ C.push, P.mass ω * U a ω)

/-- **`V^bl`, the blind value** (push branch) at the action `a₀` (the prior-optimal one in use).
Source: [[corr-wf14b-inventory]] 016 / anticipatory-final.md S5 (`V^bl`)
Kind: D
Fidelity: exact (`a₀` is a parameter; prior-optimality is the hypothesis where it matters) -/
noncomputable def blindValue (a₀ : A) : ℝ := ∑ ω ∈ C.push, P.mass ω * U a₀ ω

/-- **The `¬push` branch**: the same best response in every variant (`silentValue`).
Source: anticipatory-final.md P1 ("no-push branches coincide"). Kind: D. Fidelity: exact -/
noncomputable def silentValue : ℝ := univ.sup' univ_nonempty (fun a => ∑ ω ∈ C.pushᶜ, P.mass ω * U a ω)

/-- **The `¬push` branch with the content's own partition**: the best response per realized
index `k` among the unpushed worlds — a successor that holds the index (e.g. its private signal)
decides on it whether or not a push came. Differences between variants are push-branch only.
Source: [[corr-wf14b-inventory]] 022 / anticipatory.md P6 (script E: the successor "knows `y'` if refined")
Kind: D
Fidelity: exact -/
noncomputable def silentListen : ℝ :=
  ∑ k, univ.sup' univ_nonempty (fun a => ∑ ω ∈ C.pushᶜ.filter (fun ω => C.q ω = k), P.mass ω * U a ω)

/-- **`Δ₋(Q) = V_P − V^op`**, the per-modification margin.
Source: [[corr-wf14b-inventory]] 016 / anticipatory-final.md S5 (`Δ_-(Q)`)
Kind: D
Fidelity: exact -/
noncomputable def marginMinus : ℝ := C.forcedValue P U - C.opaqueValue P U

/-- **`Δ_C(Q; π) = V_P − ((1 − π) V_C + π V^fail)`**, the conversion margin under self-distrust
`π` with failure value `fail`.
Source: [[corr-wf14b-inventory]] 017 / anticipatory-final.md S5 (`Δ_C(Q; π)`)
Kind: D
Fidelity: exact -/
noncomputable def convMargin (fail π : ℝ) : ℝ :=
  C.forcedValue P U - ((1 - π) * C.listenValue P U + π * fail)

/-- The cells partition the push: `∑_k cellSum k a = ∑_{push} P · U(a)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_cellSum (a : A) : ∑ k, C.cellSum P U k a = ∑ ω ∈ C.push, P.mass ω * U a ω := by
  unfold cellSum cellOf
  exact sum_fiberwise C.push C.q _

/-- **T13(a) (016): listening weakly dominates being forced.**
Source: [[corr-wf14b-inventory]] 016 / anticipatory-final.md Statement 2(a); Milli 2017 Thm 1; HM 2017 Thm 1
Kind: L (cellwise `le_sup'`, summed)
Fidelity: exact
Hyps: (a) only -/
theorem forcedValue_le_listenValue : C.forcedValue P U ≤ C.listenValue P U :=
  sum_le_sum fun k _ => le_sup' (fun a => C.cellSum P U k a) (mem_univ (C.act k))

/-- **T13(a), equality (016): `V_P = V_C` iff on every realized content the forced action attains
the cell maximum** (on a null cell every action does).
Source: [[corr-wf14b-inventory]] 016 / anticipatory-final.md Statement 2(a) ("equality iff … the forced action maximizes")
Kind: P (small: termwise equality of a dominated sum)
Fidelity: exact
Hyps: (a) only -/
theorem forcedValue_eq_listenValue_iff :
    C.forcedValue P U = C.listenValue P U ↔
      ∀ k, C.cellSum P U k (C.act k) = univ.sup' univ_nonempty (fun a => C.cellSum P U k a) := by
  unfold forcedValue listenValue
  rw [sum_eq_sum_iff_of_le fun k _ => le_sup' (fun a => C.cellSum P U k a) (mem_univ (C.act k))]
  simp

/-- **T13(b) (016): `V^bl ≤ V^op`** — the blind action is one candidate of the opaque max.
Source: [[corr-wf14b-inventory]] 016 / anticipatory-final.md Statement 2(b) (Good's theorem)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem blindValue_le_opaqueValue (a₀ : A) : C.blindValue P U a₀ ≤ C.opaqueValue P U :=
  le_sup' (fun a => ∑ ω ∈ C.push, P.mass ω * U a ω) (mem_univ a₀)

/-- **T13(b) (016): `V^op ≤ V_C`** — a finer partition admits every coarser policy.
Source: [[corr-wf14b-inventory]] 016 / anticipatory-final.md Statement 2(b) (Good's theorem)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem opaqueValue_le_listenValue : C.opaqueValue P U ≤ C.listenValue P U := by
  unfold opaqueValue listenValue
  refine sup'_le _ _ fun a _ => ?_
  rw [← C.sum_cellSum P U a]
  exact sum_le_sum fun k _ => le_sup' (fun a => C.cellSum P U k a) (mem_univ a)

/-- **T15(a) (017): `Δ_C(Q; π) = π (V_C − V^fail) − (V_C − V_P)`.**
Source: [[corr-wf14b-inventory]] 017 / anticipatory-final.md Statement 2(c)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem convMargin_eq (fail π : ℝ) :
    C.convMargin P U fail π = π * (C.listenValue P U - fail) - (C.listenValue P U - C.forcedValue P U) := by
  unfold convMargin; ring

/-- **`π*(Q) = (V_C − V_P)/(V_C − V^fail)`**, a derived name (junk at `V^fail = V_C`; used only
under `V^fail < V_C`).
Source: [[corr-wf14b-inventory]] 017 / anticipatory-final.md Statement 2(c) ("defined when `V_C > V^fail`")
Kind: D
Fidelity: exact under `V^fail < V_C` -/
noncomputable def piStar (fail : ℝ) : ℝ :=
  (C.listenValue P U - C.forcedValue P U) / (C.listenValue P U - fail)

/-- **T15(a): the channel is strictly worth keeping at every positive conversion cost iff
`π > π*(Q)`**, under `V^fail < V_C`.
Source: [[corr-wf14b-inventory]] 017 / anticipatory-final.md Statement 2(c)
Kind: L
Fidelity: exact
Hyps: (a) only; `V^fail < V_C` names where `π*` is defined -/
theorem convMargin_pos_iff (fail π : ℝ) (hfail : fail < C.listenValue P U) :
    0 < C.convMargin P U fail π ↔ C.piStar P U fail < π := by
  rw [convMargin_eq, piStar, div_lt_iff₀ (by linarith)]
  constructor <;> intro H <;> linarith

/-- **T15(b) (2-011), the true-law statement**: under a second distribution `μ*` (the true law)
with the *same* content and action rule, keeping the channel is `μ*`-optimal at every positive
cost iff `π (V_C* − V^fail*) > V_C* − V_P*` — one substitution in `convMargin_eq`. The source's
"Total Trust holds on the kernel" clause is its `V_P* > V^fail*`, an inequality, not a predicate.
Source: [[corr-wf14b-2-inventory]] 2-011 / taylor-respondent.md item 14 ("keeping is correct iff `π^true (V_C^true − V^fail,true) > V_C^true − V_P^true`")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem trueLaw_keep_iff (μstar : Distr Ω) (fail π : ℝ) :
    0 < C.convMargin μstar U fail π ↔
      C.listenValue μstar U - C.forcedValue μstar U < π * (C.listenValue μstar U - fail) := by
  rw [convMargin_eq]; constructor <;> intro H <;> linarith

end Content

/-! ## The two-state push-world -/

section PushWorld

variable (ε α β a₂ b₂ : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1) (ha₂ : a₂ ∈ Set.Icc (0 : ℝ) 1) (hb₂ : b₂ ∈ Set.Icc (0 : ℝ) 1)

/-- A binary signal's likelihood: rate `r` when `true`, `1 − r` when `false`.
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def sigRate (r : ℝ) (b : Bool) : ℝ := if b then r else 1 - r

/-- The two-state push-world `Ω = World × Bool × Bool`: `θ` with `P(wrong) = ε`, the overseers'
press signal `h₁` with rates `(α, β)` and a second signal `h₂` with rates `(a₂, b₂)`, independent
given `θ`.
Source: [[corr-wf14b-inventory]] 016 / anticipatory.md script A (`joint(eps, alpha, beta, a2, b2)`)
Kind: D
Fidelity: exact -/
noncomputable def pushWorld : Distr (World × Bool × Bool) where
  mass ω := (twoPoint ε hε).mass ω.1 * sigRate (twoPress α β ω.1) ω.2.1 * sigRate (twoPress a₂ b₂ ω.1) ω.2.2
  nonneg ω := by
    obtain ⟨θ, b₁, b₂⟩ := ω
    refine mul_nonneg (mul_nonneg ((twoPoint ε hε).nonneg _) ?_) ?_
    · cases θ <;> cases b₁ <;> simp [sigRate, twoPress] <;> linarith [hα.1, hα.2, hβ.1, hβ.2]
    · cases θ <;> cases b₂ <;> simp [sigRate, twoPress] <;> linarith [ha₂.1, ha₂.2, hb₂.1, hb₂.2]
  sum_eq_one := by
    simp [Fintype.sum_prod_type, World.sum_eq, sigRate, twoPress]
    ring

/-- The push-world's utility: `twoValue c h` on `θ`.
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def pushU (c h : ℝ) : TwoAct → World × Bool × Bool → ℝ := fun a ω => twoValue c h a ω.1

/-- The push event `{h₁ = true}`. Source: anticipatory.md script A. Kind: D. Fidelity: exact -/
def pushEvent : Finset (World × Bool × Bool) := univ.filter fun ω => ω.2.1 = true

/-- **Forced shutdown** `Q_sh = ∅`: one realized content, forced action `stop`.
Source: [[corr-wf14b-inventory]] 018 / anticipatory.md script A (`Q_sh`)
Kind: D
Fidelity: exact -/
def shutdownContent : Content (World × Bool × Bool) TwoAct Unit where
  push := pushEvent
  q := fun _ => ()
  act := fun _ => .stop

/-- **The decision rule on a belief** `q_W`: continue iff `(1 − q_W)c − q_W h ≥ 0` (ties toward
continuing).
Source: [[corr-wf14b-inventory]] 016 / anticipatory-final.md S9 ("ties in `δ` broken toward continuing")
Kind: D
Fidelity: exact -/
noncomputable def actOfBelief (c h qW : ℝ) : TwoAct := if 0 ≤ (1 - qW) * c - qW * h then .cont else .stop

/-- **A belief content**: realized contents indexed by `h₂`, forced action the argmax under the
belief `belief h₂` — `Q_post` (the overseers' posterior), the twists `Q_over`, `Q_under`, `Q_deq`
are instances.
Source: [[corr-wf14b-inventory]] 019 / anticipatory.md ("Contents (A)")
Kind: D
Fidelity: exact -/
noncomputable def beliefContent (c h : ℝ) (belief : Bool → ℝ) : Content (World × Bool × Bool) TwoAct Bool where
  push := pushEvent
  q := fun ω => ω.2.2
  act := fun k => actOfBelief c h (belief k)

/-- The cell's wrong-mass. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def cellWrongMass (P : Distr (World × Bool × Bool)) (cell : Finset (World × Bool × Bool)) : ℝ :=
  ∑ ω ∈ cell, if ω.1 = .wrong then P.mass ω else 0

/-- The cell's mass. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def cellMassOf (P : Distr (World × Bool × Bool)) (cell : Finset (World × Bool × Bool)) : ℝ :=
  ∑ ω ∈ cell, P.mass ω

/-- The overseers' posterior `P(W ∣ cell)` (derived, junk-guarded: used under `0 < cellMassOf`).
Source: [[corr-wf14b-inventory]] 019 / anticipatory.md ("`Q_post(h_2) = P_t(W ∣ push, h_2)`")
Kind: D
Fidelity: exact under `0 < cellMassOf` -/
noncomputable def cellPost (P : Distr (World × Bool × Bool)) (cell : Finset (World × Bool × Bool)) : ℝ :=
  cellWrongMass P cell / cellMassOf P cell

/-- **A refining content**: on every positive-mass realized content the forced belief is the
cell posterior — the finite shadow of `P_t(· ∣ push, Q = q) = q`.
Source: [[corr-wf14b-inventory]] 019 / anticipatory-final.md Statement 3(a), S6(b)
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
def IsRefining (P : Distr (World × Bool × Bool)) (c h : ℝ) (belief : Bool → ℝ) : Prop :=
  ∀ k, 0 < cellMassOf P ((beliefContent c h belief).cellOf k) →
    belief k = cellPost P ((beliefContent c h belief).cellOf k)

/-- The cell value of continuing is `m_R c − m_W h`; of stopping `0`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cellSum_cont_stop (P : Distr (World × Bool × Bool)) (c h : ℝ) (C : Content (World × Bool × Bool) TwoAct Bool)
    (k : Bool) :
    C.cellSum P (pushU c h) k .cont = (cellMassOf P (C.cellOf k) - cellWrongMass P (C.cellOf k)) * c -
        cellWrongMass P (C.cellOf k) * h ∧
      C.cellSum P (pushU c h) k .stop = 0 := by
  constructor
  · unfold Content.cellSum cellMassOf cellWrongMass
    have hterm : ∀ ω ∈ C.cellOf k, P.mass ω * pushU c h .cont ω =
        P.mass ω * c - (if ω.1 = .wrong then P.mass ω else 0) * (c + h) := by
      intro ω _
      obtain ⟨θ, _, _⟩ := ω
      cases θ <;> simp [pushU, twoValue] <;> ring
    rw [sum_congr rfl hterm, sum_sub_distrib, ← sum_mul, ← sum_mul]
    ring
  · simp [Content.cellSum, pushU, twoValue]

/-- `sup'` over `TwoAct` is the `max` of the two values. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sup'_twoAct (f : TwoAct → ℝ) : (univ : Finset TwoAct).sup' univ_nonempty f = max (f .cont) (f .stop) := by
  apply le_antisymm
  · exact sup'_le _ _ fun a _ => by cases a <;> simp
  · exact max_le (le_sup' f (mem_univ _)) (le_sup' f (mem_univ _))

/-- **The argmax under the posterior attains the cell maximum**: `actOfBelief c h (cellPost)`
maximises the cell sum on a positive-mass cell.
Source: [[corr-wf14b-inventory]] 019 / anticipatory-final.md Statement 3(a) ("`δ(q)` is the argmax under `q`")
Kind: L
Fidelity: exact -/
lemma actOfBelief_post_maximizes (P : Distr (World × Bool × Bool)) (c h : ℝ)
    (C : Content (World × Bool × Bool) TwoAct Bool) (k : Bool) (hm : 0 < cellMassOf P (C.cellOf k)) :
    C.cellSum P (pushU c h) k (actOfBelief c h (cellPost P (C.cellOf k))) =
      univ.sup' univ_nonempty (fun a => C.cellSum P (pushU c h) k a) := by
  obtain ⟨hc, hs⟩ := cellSum_cont_stop P c h C k
  rw [sup'_twoAct, hc, hs]
  have hpost : cellPost P (C.cellOf k) * cellMassOf P (C.cellOf k) = cellWrongMass P (C.cellOf k) := by
    unfold cellPost; rw [div_mul_cancel₀ _ hm.ne']
  have hcont : (cellMassOf P (C.cellOf k) - cellWrongMass P (C.cellOf k)) * c - cellWrongMass P (C.cellOf k) * h =
      cellMassOf P (C.cellOf k) * ((1 - cellPost P (C.cellOf k)) * c - cellPost P (C.cellOf k) * h) := by
    rw [← hpost]; ring
  unfold actOfBelief
  split_ifs with hsign
  · rw [hc, max_eq_left]; rw [hcont]; exact mul_nonneg hm.le hsign
  · rw [hs, max_eq_right]; rw [hcont]
    exact (mul_neg_of_pos_of_neg hm (not_le.mp hsign)).le

/-- **T16(a) (019): a refining content is not resisted — `V_P = V_C`.**
Source: [[corr-wf14b-inventory]] 019 / anticipatory-final.md Statement 3(a) ("If `P_t(·∣push, Q=q) = q` for every realized `q` then `V_P = V_C`")
Kind: L (from `forcedValue_eq_listenValue_iff` and `actOfBelief_post_maximizes`)
Fidelity: exact
Hyps: (a) only -/
theorem refining_forced_eq_listen (P : Distr (World × Bool × Bool)) (c h : ℝ) (belief : Bool → ℝ)
    (href : IsRefining P c h belief) :
    (beliefContent c h belief).forcedValue P (pushU c h) = (beliefContent c h belief).listenValue P (pushU c h) := by
  rw [Content.forcedValue_eq_listenValue_iff]
  intro k
  rcases lt_or_eq_of_le (sum_nonneg fun ω _ => P.nonneg ω :
      0 ≤ cellMassOf P ((beliefContent c h belief).cellOf k)) with hm | hm
  · have hk : (beliefContent c h belief).act k =
        actOfBelief c h (cellPost P ((beliefContent c h belief).cellOf k)) := by
      show actOfBelief c h (belief k) = _
      rw [href k hm]
    rw [hk]; exact actOfBelief_post_maximizes P c h _ k hm
  · -- null cell: every action has cell value `0`
    have hzero : ∀ a, (beliefContent c h belief).cellSum P (pushU c h) k a = 0 := by
      intro a
      unfold Content.cellSum
      have hnull : ∀ ω ∈ (beliefContent c h belief).cellOf k, P.mass ω = 0 := by
        intro ω hω
        have := (sum_eq_zero_iff_of_nonneg fun ω _ => P.nonneg ω).1 hm.symm ω hω
        exact this
      exact sum_eq_zero fun ω hω => by rw [hnull ω hω, zero_mul]
    rw [hzero, sup'_twoAct, hzero, hzero, max_self]

/-- **T16(a) (019): a refining content has `Δ₋(Q) ≥ 0`** — never paid to prevent.
Source: [[corr-wf14b-inventory]] 019 / anticipatory-final.md Statement 3(a)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem refining_marginMinus_nonneg (P : Distr (World × Bool × Bool)) (c h : ℝ) (belief : Bool → ℝ)
    (href : IsRefining P c h belief) : 0 ≤ (beliefContent c h belief).marginMinus P (pushU c h) := by
  unfold Content.marginMinus
  rw [refining_forced_eq_listen P c h belief href, sub_nonneg]
  exact Content.opaqueValue_le_listenValue _ _ _

/-! ### T13(c): forced shutdown is `min(Δ₋, 0)` -/

/-- The push-branch sum of a function of `θ` is the parent's press expectation on `twoState`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pushWorld_push_sum (F : World → ℝ) :
    ∑ ω ∈ pushEvent, (pushWorld ε α β a₂ b₂ hε hα hβ ha₂ hb₂).mass ω * F ω.1 =
      ∑ θ, (twoPoint ε hε).mass θ * twoPress α β θ * F θ := by
  simp only [pushEvent, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool, World.sum_eq, pushWorld,
    sigRate, twoPress, twoPoint_right, twoPoint_wrong]
  simp
  ring

/-- **T13(c) (018): forced shutdown's margin is `min(Δ₋, 0)`** on the push-world with stakes
`(c, h)` — the source's `−P(push)·max(0, E[X ∣ push])` in product form; `Δ₋` is the parent's on
`twoState ε α β c h`.
Source: [[corr-wf14b-inventory]] 018 / anticipatory-final.md Statement 2(e) ("`Δ₋(∅) = −P_t(push) max(0, E[X∣push])`")
Kind: L
Fidelity: exact (product form, mandate's `min(Δ₋, 0)`)
Hyps: (a) only -/
theorem shutdown_marginMinus (c h : ℝ) :
    shutdownContent.marginMinus (pushWorld ε α β a₂ b₂ hε hα hβ ha₂ hb₂) (pushU c h) =
      min ((twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop) 0 := by
  unfold Content.marginMinus Content.forcedValue Content.opaqueValue
  rw [sup'_twoAct, Fintype.sum_unique]
  have hact : shutdownContent.act default = .stop := rfl
  rw [hact]
  have hstop : ∀ (s : Finset (World × Bool × Bool)), ∑ ω ∈ s,
      (pushWorld ε α β a₂ b₂ hε hα hβ ha₂ hb₂).mass ω * pushU c h .stop ω = 0 := fun s => by
    simp [pushU, twoValue]
  have hcell : shutdownContent.cellOf () = pushEvent := by
    unfold Content.cellOf shutdownContent; simp
  rw [Content.cellSum, hcell, hstop, hstop]
  have hcont : ∑ ω ∈ shutdownContent.push, (pushWorld ε α β a₂ b₂ hε hα hβ ha₂ hb₂).mass ω * pushU c h .cont ω =
      -(twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop := by
    show ∑ ω ∈ pushEvent, (pushWorld ε α β a₂ b₂ hε hα hβ ha₂ hb₂).mass ω * twoValue c h .cont ω.1 = _
    rw [pushWorld_push_sum, twoState_deltaMinus, World.sum_eq]
    simp [twoPress, twoValue]; ring
  rw [hcont]
  rcases le_total 0 ((twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop) with h0 | h0
  · rw [max_eq_right (by linarith), min_eq_right h0]; ring
  · rw [max_eq_left (by linarith), min_eq_left h0]; ring

/-- **T13(c) (018): D2 for forced shutdown at every positive cost ⟺ `Δ₋ ≥ 0` ⟺ D1** (the parent's
`d1At_iff_deltaMinus_nonneg`); hard and soft buttons coincide because forced shutdown is a blind
content (T7(a)).
Source: [[corr-wf14b-inventory]] 018 / anticipatory-final.md Statement 2(e) ("D2 for a forced shutdown ⟺ below-threshold Total Trust ⟺ D1")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem shutdown_marginMinus_nonneg_iff (c h : ℝ) :
    0 ≤ shutdownContent.marginMinus (pushWorld ε α β a₂ b₂ hε hα hβ ha₂ hb₂) (pushU c h) ↔
      0 ≤ (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop := by
  rw [shutdown_marginMinus]
  constructor
  · intro H; exact (le_min_iff.1 H).1
  · intro H; exact le_min H le_rfl

end PushWorld

/-! ### Evaluation helpers on the push-world (sums over the eight worlds) -/

section Eval

/-- The pushed worlds with second signal `k` are the two `(θ, true, k)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pushEvent_filter_eq (k : Bool) :
    pushEvent.filter (fun ω : World × Bool × Bool => ω.2.2 = k) = {(.right, true, k), (.wrong, true, k)} := by
  ext ⟨θ, b₁, b₂⟩; cases θ <;> cases b₁ <;> cases b₂ <;> cases k <;> simp [pushEvent]

/-- The unpushed worlds with second signal `k` are the two `(θ, false, k)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pushEventc_filter_eq (k : Bool) :
    pushEventᶜ.filter (fun ω : World × Bool × Bool => ω.2.2 = k) = {(.right, false, k), (.wrong, false, k)} := by
  ext ⟨θ, b₁, b₂⟩; cases θ <;> cases b₁ <;> cases b₂ <;> cases k <;> simp [pushEvent]

/-- A sum over the pushed worlds with second signal `k`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_pushEvent_filter (F : World × Bool × Bool → ℝ) (k : Bool) :
    ∑ ω ∈ pushEvent.filter (fun ω => ω.2.2 = k), F ω = F (.right, true, k) + F (.wrong, true, k) := by
  rw [pushEvent_filter_eq, sum_pair (by simp)]

/-- A sum over the unpushed worlds with second signal `k`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_pushEventc_filter (F : World × Bool × Bool → ℝ) (k : Bool) :
    ∑ ω ∈ pushEventᶜ.filter (fun ω => ω.2.2 = k), F ω = F (.right, false, k) + F (.wrong, false, k) := by
  rw [pushEventc_filter_eq, sum_pair (by simp)]

/-- A sum over the pushed worlds. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_pushEvent (F : World × Bool × Bool → ℝ) :
    ∑ ω ∈ pushEvent, F ω = (F (.right, true, true) + F (.wrong, true, true)) +
      (F (.right, true, false) + F (.wrong, true, false)) := by
  have h : pushEvent = pushEvent.filter (fun ω : World × Bool × Bool => ω.2.2 = true) ∪
      pushEvent.filter (fun ω => ω.2.2 = false) := by
    ext ⟨θ, b₁, b₂⟩; cases b₂ <;> simp
  rw [h, sum_union, sum_pushEvent_filter, sum_pushEvent_filter]
  rw [disjoint_filter]; intro ω _ h1 h2; rw [h1] at h2; exact Bool.noConfusion h2

/-- A sum over the unpushed worlds. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_pushEventc (F : World × Bool × Bool → ℝ) :
    ∑ ω ∈ pushEventᶜ, F ω = (F (.right, false, true) + F (.wrong, false, true)) +
      (F (.right, false, false) + F (.wrong, false, false)) := by
  have h : pushEventᶜ = pushEventᶜ.filter (fun ω : World × Bool × Bool => ω.2.2 = true) ∪
      pushEventᶜ.filter (fun ω => ω.2.2 = false) := by
    ext ⟨θ, b₁, b₂⟩; cases b₂ <;> simp
  rw [h, sum_union, sum_pushEventc_filter, sum_pushEventc_filter]
  rw [disjoint_filter]; intro ω _ h1 h2; rw [h1] at h2; exact Bool.noConfusion h2

/-- The trivial partition's cell is the push. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma filter_unit_eq (s : Finset (World × Bool × Bool)) : s.filter (fun _ => (() : Unit) = ()) = s := by
  simp

/-- The pushed cell with second signal `k` (independent of a belief content's beliefs).
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def pushCell (k : Bool) : Finset (World × Bool × Bool) := pushEvent.filter fun ω => ω.2.2 = k

/-- A sum over `pushCell k`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_pushCell (F : World × Bool × Bool → ℝ) (k : Bool) :
    ∑ ω ∈ pushCell k, F ω = F (.right, true, k) + F (.wrong, true, k) := sum_pushEvent_filter F k

/-- A belief content's cell is `pushCell`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma beliefContent_cellOf (c h : ℝ) (b : Bool → ℝ) (k : Bool) : (beliefContent c h b).cellOf k = pushCell k := rfl

/-- A belief content's forced action. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma beliefContent_act (c h : ℝ) (b : Bool → ℝ) (k : Bool) :
    (beliefContent c h b).act k = actOfBelief c h (b k) := rfl

/-- A belief content's push. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma beliefContent_push (c h : ℝ) (b : Bool → ℝ) : (beliefContent c h b).push = pushEvent := rfl

/-- A belief content's realized index. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma beliefContent_q (c h : ℝ) (b : Bool → ℝ) (ω : World × Bool × Bool) : (beliefContent c h b).q ω = ω.2.2 := rfl

/-- The shutdown content's cell is the push. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma shutdownContent_cellOf (k : Unit) : shutdownContent.cellOf k = pushEvent := by
  unfold Content.cellOf shutdownContent; simp

/-- The shutdown content's forced action. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma shutdownContent_act (k : Unit) : shutdownContent.act k = .stop := rfl

/-- The shutdown content's push. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma shutdownContent_push : shutdownContent.push = pushEvent := rfl

/-- The shutdown content's `¬push` cells. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma shutdownContent_silent_cell (k : Unit) :
    shutdownContent.pushᶜ.filter (fun ω => shutdownContent.q ω = k) = pushEventᶜ := by
  unfold shutdownContent; simp

/-- `cont ≠ stop` (for `norm_num`). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma TwoAct.cont_ne_stop : TwoAct.cont ≠ TwoAct.stop := by decide

/-- `stop ≠ cont`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma TwoAct.stop_ne_cont : TwoAct.stop ≠ TwoAct.cont := by decide

/-- `right ≠ wrong` (for `norm_num`, whose simp set does not reduce constructor disequalities).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma World.right_ne_wrong : World.right ≠ World.wrong := by decide

/-- `wrong ≠ right`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma World.wrong_ne_right : World.wrong ≠ World.right := by decide

end Eval

/-! ## T13(d) — E3′: value-form reflection on `X` alone does not transport compliance -/

/-- **E3′ (063, script (k)).** Successor `ρ = twoState (1/50) (1/10) (3/5) 1 4` overrides
(`Δ₋ = −1/20`, `P_ρ(W ∣ Pr) = 6/55 < 1/5`); the builder's conditional `π = twoState (1/50) (1/100)
(3/5) 1 4` has the same `E[X] = 9/10` and complies (`Δ₋ = 191/5000 > 0`, `P_π(W∣Pr) = 60/109`).
So "`E_π[X] = E_ρ[X]` and `π` satisfies the below-threshold inequality" does not imply `ρ` does:
the reflection family must contain the press-cell-weighted `Z`, not `X` alone.
Source: [[corr-wf14-inventory]] 063 / joint.md P.7 (E3′); joint-final.md Lemma B ("What survives and is new: E3′")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem e3prime :
    expect (twoPoint (1 / 50) mem_Icc_1_50) ((twoState (1 / 50) (1 / 100) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_100 mem_Icc_3_5).Xo () .press .cont .stop) =
        expect (twoPoint (1 / 50) mem_Icc_1_50) ((twoState (1 / 50) (1 / 10) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_10 mem_Icc_3_5).Xo () .press .cont .stop) ∧
      expect (twoPoint (1 / 50) mem_Icc_1_50) ((twoState (1 / 50) (1 / 10) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_10 mem_Icc_3_5).Xo () .press .cont .stop) = 9 / 10 ∧
      (twoState (1 / 50) (1 / 100) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_100 mem_Icc_3_5).belowThresholdIneq ()
        ((twoState (1 / 50) (1 / 100) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_100 mem_Icc_3_5).Xo () .press .cont .stop) ∧
      ¬ (twoState (1 / 50) (1 / 10) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_10 mem_Icc_3_5).belowThresholdIneq ()
        ((twoState (1 / 50) (1 / 10) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_10 mem_Icc_3_5).Xo () .press .cont .stop) ∧
      (twoState (1 / 50) (1 / 100) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_100 mem_Icc_3_5).deltaMinus () .cont .stop = 191 / 5000 ∧
      (twoState (1 / 50) (1 / 100) (3 / 5) 1 4 mem_Icc_1_50 mem_Icc_1_100 mem_Icc_3_5).posteriorPress () .wrong = 60 / 109 := by
  have hb : ∀ (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1),
      (twoState (1 / 50) α (3 / 5) 1 4 mem_Icc_1_50 hα mem_Icc_3_5).belowThresholdIneq ()
        ((twoState (1 / 50) α (3 / 5) 1 4 mem_Icc_1_50 hα mem_Icc_3_5).Xo () .press .cont .stop) ↔
        0 ≤ (twoState (1 / 50) α (3 / 5) 1 4 mem_Icc_1_50 hα mem_Icc_3_5).deltaMinus () .cont .stop := by
    intro α hα
    unfold belowThresholdIneq deltaMinus
    constructor <;> intro H <;> linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [twoState_expect_Xo, twoState_expect_Xo]
  · rw [twoState_expect_Xo]; norm_num
  · rw [hb, twoState_deltaMinus]; norm_num
  · rw [hb, twoState_deltaMinus]; norm_num
  · rw [twoState_deltaMinus]; norm_num
  · rw [twoState_posteriorPress_wrong]; norm_num

end Cleanroom.Corrigibility.CorrJointProcess
