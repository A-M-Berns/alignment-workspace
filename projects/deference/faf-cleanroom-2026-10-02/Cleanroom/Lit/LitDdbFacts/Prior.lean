import Cleanroom.Lit.LitDdbFacts.Cells
import Cleanroom.Lit.LitDdbFacts.Ladder

/-!
# Prior frames and Dorst's earlier theorems (§2 l. 157, fn 25)

Package `lit-ddb-facts`, Target 17 and extension E1. A **prior frame** `⟨W, E, μ⟩` has a
regular prior `μ` and an evidence map `E : W → Finset W` (nonempty values); the probability
frame it induces has rows `P_w = μ(· | E_w)`. DDB's fn 25 paraphrases Dorst (2020a, Theorem 7.4)
as "on prior frames Trust ⟹ Value", with the deferrer *being* the prior `μ`.

**That paraphrase is false as stated** (audit round 2, B1): `ExamplesPrior.cxQ`, a three-world
prior frame with factive evidence `E_0 = {0}`, `E_1 = {0, 1}`, `E_2 = {1, 2}` and prior
`(1/10, 3/10, 3/5)`, has `Trust μ` and `¬ Value μ` (`ExamplesPrior.prior_trust_value_refuted`).
The rows of record here are what survives:

* Simple Trust of the prior forces the evidence to be factive (`PriorFrame.mem_Ev_self_of_simpleTrust`)
  and *mass-monotone*: `v ∈ E_w → μ(E_v) ≤ μ(E_w)` (`PriorFrame.mass_Ev_le_of_mem_of_simpleTrust`).
* On a **nested** prior frame (any two evidence sets that meet are comparable,
  `PriorFrame.Nested`) mass-monotonicity makes the evidence transitive (`v ∈ E_w → E_v ⊆ E_w`),
  and then the prior **totally trusts** the induced frame
  (`PriorFrame.totalTrust_of_nested_of_simpleTrust`), by an induction over evidence-closed sets.
  So on nested prior frames Simple Trust, Trust, Total Trust and Value of the prior coincide
  (`PriorFrame.tfae_nested`); in particular Trust ⟹ Value (`prior_value_of_trust_of_nested`),
  which is the nearest true version of the theorem fn 25 attributes to Dorst. The counterexample
  is not nested (`E_1 ∩ E_2 = {1}` with neither containing the other), and the round-2 audit's
  exhaustive search on three worlds found no failing nested evidence map.
* The separate-deferrer reading on nested prior frames (`∀ π ∈ Δ, Trust π → Value π`) stays OPEN
  (`prior_trust_value_all_nested_open`, `lit-ddb-facts-open.txt`): Simple Trust of a separate
  deferrer is *not* enough (`ExamplesPrior.chainQ_simpleTrust_not_value`), and the proof sketch
  through full Trust is recorded in the report.

Fact 2.1's `fact21`, Figure 2 and Figure 3 are shown not to be prior frames (Target 17(iii)).
-/

namespace Cleanroom.Lit.LitDdbFacts

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- A **prior frame**: a regular prior `μ` on `W` and an evidence map `Ev`. Fn 25 does not say the
evidence is nonempty, but presupposes it (`μ(· | ∅)` is undefined, and "recover a probability
frame" needs every row to be a distribution), so nonemptiness is carried as a field. Neither
factivity (`w ∈ E_w`) nor nestedness is assumed: the first is *forced* by Simple Trust of the prior
(`PriorFrame.mem_Ev_self_of_simpleTrust`), the second is the hypothesis under which the
Trust ⟹ Value theorem holds (`prior_value_of_trust_of_nested`) and without which it fails
(`ExamplesPrior.cxQ`).
Source: [[Deference Done Better]] fn 25
Kind: D
Fidelity: exact (nonempty evidence made explicit; see docstring) -/
structure PriorFrame (W : Type) [Fintype W] where
  /-- the prior -/
  μ : W → ℝ
  /-- regularity -/
  μ_pos : ∀ w, 0 < μ w
  /-- the prior is a distribution -/
  μ_sum : ∑ w, μ w = 1
  /-- the evidence at each world -/
  Ev : W → Finset W
  /-- evidence is never contradictory -/
  Ev_nonempty : ∀ w, (Ev w).Nonempty

/-- The prior is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem PriorFrame.μ_mem (Q : PriorFrame W) : Q.μ ∈ stdSimplex ℝ W :=
  ⟨fun w => (Q.μ_pos w).le, Q.μ_sum⟩

/-- Evidence has positive prior mass (regularity and nonemptiness).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem PriorFrame.mass_Ev_pos (Q : PriorFrame W) (w : W) : 0 < mass Q.μ (Q.Ev w) := by
  obtain ⟨v, hv⟩ := Q.Ev_nonempty w
  exact mass_pos_of_mem (fun u => (Q.μ_pos u).le) hv (Q.μ_pos v)

/-- The row `P_w = μ(· | E_w)` of a prior frame (a ratio is fine here: `μ(E_w) > 0` by
regularity).
Source: [[Deference Done Better]] fn 25
Kind: D
Fidelity: exact -/
def PriorFrame.row (Q : PriorFrame W) (w : W) : W → ℝ :=
  fun v => if v ∈ Q.Ev w then Q.μ v / mass Q.μ (Q.Ev w) else 0

/-- Each row is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem PriorFrame.row_mem (Q : PriorFrame W) (w : W) : Q.row w ∈ stdSimplex ℝ W := by
  refine ⟨fun v => ?_, ?_⟩
  · unfold PriorFrame.row
    split_ifs
    · exact div_nonneg (Q.μ_pos v).le (Q.mass_Ev_pos w).le
    · exact le_rfl
  · unfold PriorFrame.row
    rw [sum_ite_mem, univ_inter]
    simp_rw [div_eq_mul_inv]
    rw [← sum_mul]
    exact mul_inv_cancel₀ (Q.mass_Ev_pos w).ne'

/-- The probability frame induced by a prior frame: `P_w := μ(· | E_w)`.
Source: [[Deference Done Better]] fn 25 ("we can then recover a probability frame by defining
`P_w = π(· | E_w)`")
Kind: D
Fidelity: exact -/
def PriorFrame.toFrame (Q : PriorFrame W) : Frame W := ⟨Q.row, Q.row_mem⟩

/-- **Target 17(i).** Value implies Trust on any frame (Dorst 2020a Theorem 7.2, via Theorem
2.2 and `TotalTrust.trust`).
Source: [[Deference Done Better]] §2 l. 157 ("Trust follows from Value (Dorst 2020a, Theorem
7.2)")
Kind: L
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` -/
theorem trust_of_value {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W} (h : Value π F) :
    Trust π F :=
  ((value_iff_totalTrust hπ F).1 h).trust hπ.1

/-! ## Target 17(iii): DDB's counterexamples are not prior frames -/

/-- A fully supported row of a prior frame is the prior itself (`E_w = W`).
Source: none: infrastructure (Target 17(iii))
Kind: L
Fidelity: n/a -/
theorem PriorFrame.row_eq_μ_of_full (Q : PriorFrame W) {w : W} (hfull : ∀ v, 0 < Q.row w v) :
    Q.row w = Q.μ := by
  have hEv : Q.Ev w = univ := by
    apply eq_univ_of_forall
    intro v
    by_contra hv
    have := hfull v
    simp [PriorFrame.row, hv] at this
  funext v
  simp [PriorFrame.row, hEv, mass_univ Q.μ_mem]

/-- **Target 17(iii).** A frame with two distinct fully supported rows is not induced by any
prior frame: both rows would be the prior.
Source: [[Deference Done Better]] fn 25; item 079 (does DDB refute Dorst?)
Kind: N-
Fidelity: n/a (a structural observation about the examples)
Hyps: (a) none -/
theorem no_priorFrame_of_two_full_rows (F : Frame W) {w v : W} (hw : ∀ u, 0 < F.P w u)
    (hv : ∀ u, 0 < F.P v u) (hne : F.P w ≠ F.P v) : ¬ ∃ Q : PriorFrame W, Q.toFrame = F := by
  rintro ⟨Q, rfl⟩
  apply hne
  show Q.row w = Q.row v
  rw [Q.row_eq_μ_of_full hw, Q.row_eq_μ_of_full hv]

/-- Figure 2's frame is not a prior frame.
Source: [[Deference Done Better]] §1 l. 104, fn 25
Kind: N-
Fidelity: n/a
Hyps: (a) none -/
theorem fig2_not_priorFrame : ¬ ∃ Q : PriorFrame (Fin 2), Q.toFrame = Examples.fig2 :=
  no_priorFrame_of_two_full_rows Examples.fig2 (w := 0) (v := 1)
    (fun u => by fin_cases u <;> norm_num [Examples.fig2_P0])
    (fun u => by fin_cases u <;> norm_num [Examples.fig2_P1]) Examples.fig2_ne

/-- Figure 3's frame is not a prior frame.
Source: [[Deference Done Better]] §1 l. 130, fn 25
Kind: N-
Fidelity: n/a
Hyps: (a) none -/
theorem fig3_not_priorFrame : ¬ ∃ Q : PriorFrame (Fin 2), Q.toFrame = Examples.fig3 :=
  no_priorFrame_of_two_full_rows Examples.fig3 (w := 0) (v := 1)
    (fun u => by fin_cases u <;> norm_num [Examples.fig3_P0])
    (fun u => by fin_cases u <;> norm_num [Examples.fig3_P1]) Examples.fig3_ne

/-- Fact 2.1's frame is not a prior frame. (So DDB's Trust-without-Value example does not bear on
prior frames either way; the prior-frame version of "Trust without Value" is `ExamplesPrior.cxQ`.)
Source: [[Deference Done Better]] §2 l. 161, fn 25; item 079
Kind: N-
Fidelity: n/a
Hyps: (a) none -/
theorem fact21_not_priorFrame : ¬ ∃ Q : PriorFrame (Fin 3), Q.toFrame = Examples.fact21 := by
  obtain ⟨h0, h1, _⟩ := Examples.fact21_P
  refine no_priorFrame_of_two_full_rows Examples.fact21 (w := 0) (v := 1)
    (fun u => by fin_cases u <;> norm_num [h0, Examples.vec3_two, Examples.fin3_mk_two])
    (fun u => by fin_cases u <;> norm_num [h1, Examples.vec3_two, Examples.fin3_mk_two]) ?_
  intro h
  have := congrFun h 0
  rw [h0, h1] at this
  norm_num at this

/-! ## Prior frames: Simple Trust of the prior forces factive, mass-monotone evidence -/

/-- A row of a prior frame is certain of its own evidence: `μ(E_w | E_w) = 1`.
Source: none: infrastructure (fn 25)
Kind: L
Fidelity: n/a -/
theorem PriorFrame.mass_row_Ev (Q : PriorFrame W) (w : W) : mass (Q.row w) (Q.Ev w) = 1 := by
  have hrow : ∀ v ∈ Q.Ev w, Q.row w v = Q.μ v / mass Q.μ (Q.Ev w) := fun v hv => by
    simp [PriorFrame.row, hv]
  show ∑ v ∈ Q.Ev w, Q.row w v = 1
  rw [sum_congr rfl hrow]
  simp_rw [div_eq_mul_inv]
  rw [← sum_mul]
  exact mul_inv_cancel₀ (Q.mass_Ev_pos w).ne'

/-- Under Simple Trust of the prior, the event `[P(E_w) ≥ 1]` (the worlds whose row is certain
of `E_w`) is contained in `E_w`: it contains `w`, so has positive prior mass, and Simple Trust at
`(E_w, 1)` gives `μ(A) ≤ μ(E_w ∩ A)`, which by regularity forces `A \ E_w = ∅`.
Source: none: infrastructure (Target 17(ii)/E1, audit r1 NB5)
Kind: P
Fidelity: n/a -/
theorem PriorFrame.probEvent_Ev_subset_of_simpleTrust (Q : PriorFrame W)
    (h : SimpleTrust Q.μ Q.toFrame) (w : W) : Q.toFrame.probEvent (Q.Ev w) 1 ⊆ Q.Ev w := by
  set A := Q.toFrame.probEvent (Q.Ev w) 1 with hA
  have hμ : ∀ u, 0 ≤ Q.μ u := fun u => (Q.μ_pos u).le
  have hwA : w ∈ A := by
    rw [hA, Frame.probEvent, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    show 1 ≤ mass (Q.row w) (Q.Ev w)
    rw [Q.mass_row_Ev]
  have hpos : 0 < mass Q.μ A := mass_pos_of_mem hμ hwA (Q.μ_pos w)
  have hst := h (Q.Ev w) 1 hpos
  rw [one_mul] at hst
  have hsplit := mass_inter_add_mass_sdiff Q.μ A (Q.Ev w)
  rw [inter_comm] at hsplit
  have hnn := mass_nonneg hμ (A \ Q.Ev w)
  intro v hv
  by_contra hvE
  have : 0 < mass Q.μ (A \ Q.Ev w) :=
    mass_pos_of_mem hμ (mem_sdiff.2 ⟨hv, hvE⟩) (Q.μ_pos v)
  linarith

/-- **Simple Trust of the prior forces nested evidence to be factive**: if `E_v ⊆ E_w` then
`v ∈ E_w` (the row at `v` is certain of `E_w`, so `v` lies in the event of
`probEvent_Ev_subset_of_simpleTrust`). The special case `v = w` is factivity, `w ∈ E_w`, which
fn 25's definition of a prior frame does not assume.
Source: [[Deference Done Better]] fn 25 (prior frames); Target 17(ii)/E1 (a structural
consequence of Trust on prior frames, audit r1 NB5)
Kind: P
Fidelity: n/a
Hyps: (a) none beyond Simple Trust of the prior -/
theorem PriorFrame.mem_Ev_of_subset_of_simpleTrust (Q : PriorFrame W)
    (h : SimpleTrust Q.μ Q.toFrame) {v w : W} (hsub : Q.Ev v ⊆ Q.Ev w) : v ∈ Q.Ev w := by
  apply Q.probEvent_Ev_subset_of_simpleTrust h w
  rw [Frame.probEvent, mem_filter]
  refine ⟨mem_univ _, ?_⟩
  show 1 ≤ mass (Q.row v) (Q.Ev w)
  rw [← Q.mass_row_Ev v]
  exact mass_mono (Q.row_mem v).1 hsub

/-- **Factivity from Simple Trust of the prior**: `w ∈ E_w` at every world.
Source: [[Deference Done Better]] fn 25; Target 17(ii)/E1
Kind: P
Fidelity: n/a
Hyps: (a) none beyond Simple Trust of the prior -/
theorem PriorFrame.mem_Ev_self_of_simpleTrust (Q : PriorFrame W)
    (h : SimpleTrust Q.μ Q.toFrame) (w : W) : w ∈ Q.Ev w :=
  Q.mem_Ev_of_subset_of_simpleTrust h (subset_refl _)

/-- **Factivity from Trust of the prior**: `w ∈ E_w` at every world. So every reading of
"Trust ⟹ Value on prior frames" concerns factive evidence only, although `PriorFrame` does not
assume it.
Source: [[Deference Done Better]] fn 25; Target 17(ii)/E1
Kind: C
Fidelity: n/a
Hyps: (a) none beyond Trust of the prior -/
theorem PriorFrame.mem_Ev_self_of_trust (Q : PriorFrame W) (h : Trust Q.μ Q.toFrame) (w : W) :
    w ∈ Q.Ev w :=
  Q.mem_Ev_self_of_simpleTrust (simpleTrust_of_trust h) w

/-- **Simple Trust of the prior forces mass-monotone evidence**: `v ∈ E_w → μ(E_v) ≤ μ(E_w)`.
Simple Trust at `q = {v}`, `t = μ(v | E_w)`: the event `[P({v}) ≥ t]` contains `w`, so has
positive mass, so `v` must lie in it (else `μ({v} ∩ [P({v}) ≥ t]) = 0 < t · μ[…]`), i.e.
`μ(v | E_v) ≥ μ(v | E_w)`.
Source: none: new (Target 17(ii)/E1, repair round 2)
Kind: P
Fidelity: n/a
Hyps: (a) none beyond Simple Trust of the prior -/
theorem PriorFrame.mass_Ev_le_of_mem_of_simpleTrust (Q : PriorFrame W)
    (h : SimpleTrust Q.μ Q.toFrame) {v w : W} (hv : v ∈ Q.Ev w) :
    mass Q.μ (Q.Ev v) ≤ mass Q.μ (Q.Ev w) := by
  have hμ : ∀ u, 0 ≤ Q.μ u := fun u => (Q.μ_pos u).le
  have hmv := Q.mass_Ev_pos v
  have hmw := Q.mass_Ev_pos w
  have htpos : 0 < Q.μ v / mass Q.μ (Q.Ev w) := div_pos (Q.μ_pos v) hmw
  set A := Q.toFrame.probEvent {v} (Q.μ v / mass Q.μ (Q.Ev w)) with hA
  have hwA : w ∈ A := by
    rw [hA, Frame.probEvent, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    show _ ≤ mass (Q.row w) {v}
    rw [mass_singleton, PriorFrame.row, if_pos hv]
  have hpos : 0 < mass Q.μ A := mass_pos_of_mem hμ hwA (Q.μ_pos w)
  have hst := h {v} _ hpos
  have hvA : v ∈ A := by
    by_contra hnot
    have h0 : mass Q.μ ({v} ∩ A) = 0 := by
      rw [singleton_inter_of_notMem hnot]
      simp [mass]
    rw [h0] at hst
    exact absurd hst (not_le.2 (mul_pos htpos hpos))
  rw [hA, Frame.probEvent, mem_filter] at hvA
  have h2 : Q.μ v / mass Q.μ (Q.Ev w) ≤ Q.μ v / mass Q.μ (Q.Ev v) := by
    have := hvA.2
    change _ ≤ mass (Q.row v) {v} at this
    rwa [mass_singleton, PriorFrame.row, if_pos (Q.mem_Ev_self_of_simpleTrust h v)] at this
  exact (div_le_div_iff_of_pos_left (Q.μ_pos v) hmw hmv).1 h2

/-! ## Nested prior frames: Trust ⟹ Value (Target 17(ii), the true version) -/

/-- **Nested evidence**: any two evidence sets that meet are comparable under inclusion. This is
the hypothesis under which "Trust ⟹ Value" holds on prior frames; the counterexample
`ExamplesPrior.cxQ` is not nested.
Source: none: new (Target 17(ii)/E1, repair round 2; the Geanakoplos-shaped condition the mandate
anticipated)
Kind: D
Fidelity: n/a -/
def PriorFrame.Nested (Q : PriorFrame W) : Prop :=
  ∀ v w, (Q.Ev v ∩ Q.Ev w).Nonempty → Q.Ev v ⊆ Q.Ev w ∨ Q.Ev w ⊆ Q.Ev v

/-- A set of worlds is **evidence-closed** when it contains the evidence at each of its worlds.
Source: none: infrastructure (the induction variable of `totalTrust_of_factive_of_trans_of_nested`)
Kind: D
Fidelity: n/a -/
def PriorFrame.EvClosed (Q : PriorFrame W) (T : Finset W) : Prop := ∀ v ∈ T, Q.Ev v ⊆ T

/-- **On a nested prior frame, Simple Trust of the prior makes the evidence transitive**:
`v ∈ E_w → E_v ⊆ E_w`. Nestedness gives `E_v ⊆ E_w` or `E_w ⊆ E_v` (they share `v`), and in the
second case mass-monotonicity `μ(E_v) ≤ μ(E_w)` with regularity forces `E_v = E_w`.
Source: none: new (Target 17(ii)/E1, repair round 2)
Kind: P
Fidelity: n/a
Hyps: (a) none beyond nestedness and Simple Trust of the prior -/
theorem PriorFrame.Ev_subset_of_mem_of_nested (Q : PriorFrame W) (hn : Q.Nested)
    (h : SimpleTrust Q.μ Q.toFrame) {v w : W} (hv : v ∈ Q.Ev w) : Q.Ev v ⊆ Q.Ev w := by
  have hvv := Q.mem_Ev_self_of_simpleTrust h v
  rcases hn v w ⟨v, mem_inter.2 ⟨hvv, hv⟩⟩ with h1 | h2
  · exact h1
  · intro x hx
    by_contra hxw
    have hμ : ∀ u, 0 ≤ Q.μ u := fun u => (Q.μ_pos u).le
    have hle := Q.mass_Ev_le_of_mem_of_simpleTrust h hv
    have hsplit := mass_inter_add_mass_sdiff Q.μ (Q.Ev v) (Q.Ev w)
    rw [inter_eq_right.2 h2] at hsplit
    have : 0 < mass Q.μ (Q.Ev v \ Q.Ev w) :=
      mass_pos_of_mem hμ (mem_sdiff.2 ⟨hx, hxw⟩) (Q.μ_pos x)
    linarith

/-- The sum of `μ_w (X_w − s)` over the evidence at `u` is `μ(E_u)` times the row's slack
`E_{P_u}(X) − s` (the rows are conditionalisations of `μ`).
Source: none: infrastructure (Target 17(ii), nested case)
Kind: L
Fidelity: n/a -/
theorem PriorFrame.sum_Ev_eq_mass_mul (Q : PriorFrame W) (u : W) (X : W → ℝ) (s : ℝ) :
    ∑ w ∈ Q.Ev u, Q.μ w * (X w - s) = mass Q.μ (Q.Ev u) * (E (Q.row u) X - s) := by
  have hm : mass Q.μ (Q.Ev u) ≠ 0 := (Q.mass_Ev_pos u).ne'
  have hE : mass Q.μ (Q.Ev u) * E (Q.row u) X = ∑ w ∈ Q.Ev u, Q.μ w * X w := by
    unfold E PriorFrame.row
    simp_rw [ite_mul, zero_mul]
    rw [sum_ite_mem, univ_inter, mul_sum]
    refine sum_congr rfl fun w _ => ?_
    rw [← mul_assoc, mul_div_cancel₀ _ hm]
  rw [mul_sub, hE, mass, sum_mul, ← sum_sub_distrib]
  exact sum_congr rfl fun w _ => by ring

/-- **Total Trust of the prior on a factive, transitive, nested prior frame.** Write
`f w = μ_w (X_w − s)` and `g w = f w · 𝟙[E_{P_w}(X) ≥ s]` (the Total Trust summand). By strong
induction over evidence-closed sets `T`: `∑_T g ≥ 0` and `∑_T g ≥ ∑_T f`. Take `u ∈ T` with
`E_u` of maximal size. If `E_u ≠ T`, then `E_u` and `T \ E_u` are both closed (the second by
nestedness and maximality) and the two sums split. If `E_u = T`, let `S = {v ∈ T : E_v = T}`
(the worlds whose row is `P_u`); `T \ S` is closed and smaller, and `∑_T f = μ(T)(E_{P_u}(X) − s)`
has the sign of the indicator at `u`: if `u` is in the event, `g = f` on `S` and `∑_T f ≥ 0`;
otherwise `g = 0` on `S` and `∑_T f < 0`. Either way both inequalities pass to `T`.
Source: none: new (Target 17(ii)/E1, repair round 2)
Kind: P
Fidelity: n/a
Hyps: (a) factivity, transitivity and nestedness of the evidence (the first two are derived from
Simple Trust in `totalTrust_of_nested_of_simpleTrust`) -/
theorem PriorFrame.totalTrust_of_factive_of_trans_of_nested (Q : PriorFrame W)
    (hfact : ∀ w, w ∈ Q.Ev w) (htrans : ∀ v w, v ∈ Q.Ev w → Q.Ev v ⊆ Q.Ev w) (hn : Q.Nested) :
    TotalTrust Q.μ Q.toFrame := by
  intro X s
  set f : W → ℝ := fun w => Q.μ w * (X w - s) with hf
  set g : W → ℝ := fun w => Q.μ w * (X w - s) * (if s ≤ E (Q.row w) X then 1 else 0) with hg
  show 0 ≤ ∑ w, g w
  have key : ∀ T : Finset W, Q.EvClosed T →
      0 ≤ ∑ w ∈ T, g w ∧ ∑ w ∈ T, f w ≤ ∑ w ∈ T, g w := by
    intro T
    induction T using Finset.strongInduction with
    | H T ih =>
      intro hT
      rcases T.eq_empty_or_nonempty with rfl | hne
      · simp
      obtain ⟨u, huT, humax⟩ := exists_max_image T (fun v => (Q.Ev v).card) hne
      have hMT : Q.Ev u ⊆ T := hT u huT
      by_cases hMeq : Q.Ev u = T
      · -- `T` is the evidence at `u`
        set S := T.filter (fun v => Q.Ev v = T) with hS
        have huS : u ∈ S := mem_filter.2 ⟨huT, hMeq⟩
        have hSsub : S ⊆ T := filter_subset _ _
        have hTS : Q.EvClosed (T \ S) := by
          intro v hv x hx
          rw [mem_sdiff] at hv ⊢
          refine ⟨hT v hv.1 hx, fun hxS => hv.2 ?_⟩
          rw [hS, mem_filter] at hxS ⊢
          refine ⟨hv.1, Subset.antisymm (hT v hv.1) ?_⟩
          rw [← hxS.2]
          exact htrans x v hx
        have hlt : T \ S ⊂ T := sdiff_ssubset hSsub ⟨u, huS⟩
        obtain ⟨ih1, ih2⟩ := ih (T \ S) hlt hTS
        have hsplitf := sum_sdiff (f := f) hSsub
        have hsplitg := sum_sdiff (f := g) hSsub
        have hrow : ∀ v ∈ S, Q.row v = Q.row u := by
          intro v hv
          rw [hS, mem_filter] at hv
          funext x
          simp only [PriorFrame.row, hv.2, hMeq]
        have hT_eq : ∑ w ∈ T, f w = mass Q.μ (Q.Ev u) * (E (Q.row u) X - s) := by
          rw [← Q.sum_Ev_eq_mass_mul, hMeq]
        by_cases huA : s ≤ E (Q.row u) X
        · have hSg : ∑ w ∈ S, g w = ∑ w ∈ S, f w := by
            refine sum_congr rfl fun v hv => ?_
            simp only [hg, hf, hrow v hv, huA, if_true, mul_one]
          have hpos : 0 ≤ ∑ w ∈ T, f w := by
            rw [hT_eq]
            exact mul_nonneg (Q.mass_Ev_pos u).le (sub_nonneg.2 huA)
          constructor <;> linarith
        · have hSg : ∑ w ∈ S, g w = 0 := by
            refine sum_eq_zero fun v hv => ?_
            simp only [hg, hrow v hv, huA, if_false, mul_zero]
          have hneg : ∑ w ∈ T, f w < 0 := by
            rw [hT_eq]
            exact mul_neg_of_pos_of_neg (Q.mass_Ev_pos u) (sub_neg.2 (not_le.1 huA))
          constructor <;> linarith
      · -- the evidence at `u` is a proper closed part of `T`, and so is the rest
        have hMlt : Q.Ev u ⊂ T := Finset.ssubset_iff_subset_ne.2 ⟨hMT, hMeq⟩
        have hMcl : Q.EvClosed (Q.Ev u) := fun v hv => htrans v u hv
        have hTM : Q.EvClosed (T \ Q.Ev u) := by
          intro v hv x hx
          rw [mem_sdiff] at hv ⊢
          refine ⟨hT v hv.1 hx, fun hxM => hv.2 ?_⟩
          rcases hn v u ⟨x, mem_inter.2 ⟨hx, hxM⟩⟩ with h1 | h2
          · exact h1 (hfact v)
          · have : Q.Ev u = Q.Ev v := eq_of_subset_of_card_le h2 (humax v hv.1)
            rw [this]
            exact hfact v
        have hlt : T \ Q.Ev u ⊂ T := sdiff_ssubset hMT ⟨u, hfact u⟩
        obtain ⟨ihM1, ihM2⟩ := ih _ hMlt hMcl
        obtain ⟨ihD1, ihD2⟩ := ih _ hlt hTM
        have hsplitf := sum_sdiff (f := f) hMT
        have hsplitg := sum_sdiff (f := g) hMT
        constructor <;> linarith
  exact (key univ fun v _ => subset_univ _).1

/-- **Target 17(ii), the true version — on a nested prior frame, Simple Trust of the prior
implies Total Trust of the prior.** Simple Trust forces factive, transitive evidence
(`mem_Ev_self_of_simpleTrust`, `Ev_subset_of_mem_of_nested`) and the induction of
`totalTrust_of_factive_of_trans_of_nested` does the rest. The nestedness hypothesis is not an
artifact: without it the conclusion fails even from full Trust (`ExamplesPrior.cxQ`).
Source: [[Deference Done Better]] §2 l. 157, fn 25 (Dorst 2020a Theorem 7.4, as paraphrased there;
ATTRIBUTION-UNVETTED whether Dorst's own hypotheses are nestedness); corrected from the false
unrestricted paraphrase (audit r2 B1, findings F15)
Kind: P
Fidelity: stronger: Simple Trust (not Trust) as antecedent, Total Trust as consequent; restricted
to nested evidence, which is where the unrestricted claim fails
Hyps: (a) `hn : Q.Nested` (the hypothesis of the theorem); nothing else beyond the antecedent -/
theorem PriorFrame.totalTrust_of_nested_of_simpleTrust (Q : PriorFrame W) (hn : Q.Nested)
    (h : SimpleTrust Q.μ Q.toFrame) : TotalTrust Q.μ Q.toFrame :=
  Q.totalTrust_of_factive_of_trans_of_nested (Q.mem_Ev_self_of_simpleTrust h)
    (fun _ _ hv => Q.Ev_subset_of_mem_of_nested hn h hv) hn

/-- **Target 17(ii), deferrer-is-the-prior reading, on nested prior frames: Trust ⟹ Value.**
The nearest true version of DDB's fn 25 paraphrase of Dorst 2020a Theorem 7.4; the unrestricted
statement is refuted by `ExamplesPrior.cxQ`.
Source: [[Deference Done Better]] §2 l. 157, fn 25; Dorst 2020a Theorem 7.4 (as paraphrased;
ATTRIBUTION-UNVETTED); findings F15
Kind: C
Fidelity: variant: restricted to nested evidence (the unrestricted paraphrase is false)
Hyps: (a) `hn : Q.Nested` -/
theorem prior_value_of_trust_of_nested (Q : PriorFrame W) (hn : Q.Nested)
    (h : Trust Q.μ Q.toFrame) : Value Q.μ Q.toFrame :=
  (value_iff_totalTrust Q.μ_mem Q.toFrame).2
    (Q.totalTrust_of_nested_of_simpleTrust hn (simpleTrust_of_trust h))

/-- **On a nested prior frame the prior's Simple Trust, Trust, Total Trust and Value coincide.**
Source: [[Deference Done Better]] §2 l. 157, fn 25 (extension of the corrected Theorem 7.4
paraphrase); findings F15
Kind: C
Fidelity: stronger: the collapse of the whole ladder, not only Trust ⟹ Value
Hyps: (a) `hn : Q.Nested` -/
theorem PriorFrame.tfae_nested (Q : PriorFrame W) (hn : Q.Nested) :
    List.TFAE [SimpleTrust Q.μ Q.toFrame, Trust Q.μ Q.toFrame, TotalTrust Q.μ Q.toFrame,
      Value Q.μ Q.toFrame] := by
  tfae_have 1 → 3 := Q.totalTrust_of_nested_of_simpleTrust hn
  tfae_have 3 → 2 := TotalTrust.trust Q.μ_mem.1
  tfae_have 2 → 1 := simpleTrust_of_trust
  tfae_have 3 ↔ 4 := (value_iff_totalTrust Q.μ_mem Q.toFrame).symm
  tfae_finish

/-- **Target 17(ii), separate-deferrer reading on nested prior frames — OPEN.** Every distribution
that trusts a nested prior frame values it. Simple Trust of a separate deferrer is *not* enough
(`ExamplesPrior.chainQ_simpleTrust_not_value`), so this genuinely needs Trust's conditional
tests; the round-2 audit's exhaustive search on three worlds found no counterexample, and a proof
sketch (Trust forces `π/μ` constant on each `{v : E_v = E}` and monotone down the evidence tree,
whence `π` is a convex combination of the rows and Total Trust follows from
`totalTrust_of_factive_of_trans_of_nested`'s closed-set inequality) is in the report, E1.
The unrestricted statement (no nestedness) is refuted by `ExamplesPrior.cxQ`.
Source: [[Deference Done Better]] §2 l. 157, fn 25; Dorst 2020a Theorem 7.4 (whether Dorst
quantifies the deferrer separately is itself unverified)
Kind: OPEN
Fidelity: variant: the deferrer quantified separately from the prior; restricted to nested evidence
Hyps: (a) `hn : Q.Nested`, `hπ : π ∈ stdSimplex ℝ W`; the statement itself is open -/
theorem prior_trust_value_all_nested_open (Q : PriorFrame W) (hn : Q.Nested) {π : W → ℝ}
    (hπ : π ∈ stdSimplex ℝ W) (h : Trust π Q.toFrame) : Value π Q.toFrame := by
  sorry

end

end Cleanroom.Lit.LitDdbFacts
