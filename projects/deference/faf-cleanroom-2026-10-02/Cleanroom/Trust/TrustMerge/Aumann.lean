import Cleanroom.Trust.TtFiniteFrames.Corr
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# `trust-merge` · Aumann: two-agent agreement on a proper common-knowledge event; the modest
disagreement witness (T9(1), T9(2))

**trust-lab-2-036.** (1) **Aumann 1976, instantiated** (`aumann_two_agent`): finite worlds, a
full-support common prior `π`, two partitional correspondences `E1, E2` (`tt-finite-frames`'s
`Corr.Partitional`), an event `C` that is a union of `E1`-cells and of `E2`-cells
(`SelfEvident`), nonempty; if agent `i`'s posterior of `X` equals `q_i` on every `E_i`-cell
inside `C`, then `q_1 = q_2 = 𝔼_π(X | C)`. The engine is **partition averaging**
(`partition_averaging`): over a self-evident event a partitional agent's constant cell-posterior
is the event's posterior — the fibrewise regrouping `Σ_C = Σ_{cells} Σ_{cell}`, each cell
contributing `q · mass(cell)`. (The idea's source is the lab's `run2/lean/aumann-modesty.lean`
`partition_averaging`, single-agent, `C = univ`, cells given as two Boolean masks; this is the
general lemma over `Corr`, re-proved, not imported.) The concrete instance
`aumann_two_agent_example` has five worlds, two *different* partitions, a non-constant `X` and a
**proper** `C ≠ univ`, with `C ≠ univ`, nonemptiness and self-evidence compiled.

(2) **T9(2): the closed reading refuted; the surviving witness is not a modesty phenomenon;
transitivity is what the refutation needs.** The source asks for a partitional agent 1 and a
reflexive, transitive, **non-partitional** agent 2 "sharing" a common-knowledge event `C` with
constant cell-posteriors `q₁ ≠ q₂`. With `C` closed under both correspondences (self-evident to
both — common knowledge in the standard sense) no such data exist: for *any* reflexive transitive
`K` and `K`-closed `C`, constant `K`-cell posteriors on `C` force the `C`-posterior to that
constant (`preorder_averaging`; engine `sum_centred_eq_zero_of_cells`, an induction on `|C|`
removing a cell of least cardinality, which is an equivalence class that every other cell of `C`
either misses or contains — no Möbius machinery; proved in repair round 1, audit r1 B3). Hence
`aumann_two_agent_preorder` and `modest_disagreement_closed_refuted`: **the source's (2) in the
closed reading is unsatisfiable.** Literature placement (from memory, not re-checked against the
texts in this run — audit r2 adversarial N11): this is Samet's agreement theorem for
non-partitional information structures ("Ignoring ignorance and agreeing to disagree", *J. Econ.
Theory* 52, 1990; nondelusion = reflexivity, knowing-that-you-know = transitivity), so the source
asks for what a known theorem forbids, and this package's contribution is the kernel-checked
instance, not the fact.

**The surviving instance exhibits disagreement without common knowledge, not modest
disagreement** (repair round 2, audit r2 B1, both lenses). `noCommonKnowledge_disagreement_witness`
(round 0's `modest_disagreement_witness`, renamed): four worlds, uniform prior, agent 1
partitional with `C = {0,1}` one of its cells, agent 2 the reflexive transitive non-partitional
`K 0 = {0,1,2}, K 1 = {1}, K 2 = {2}, K 3 = {3}`, `X = (0, 1/2, 1, 0)`: cell-posteriors `1/4` vs
`1/2` on `C`, computed. But `C` is not closed under `K` (`K 0 ⊄ C`), and the non-partitional
structure is **inert**: the partition `{0,2}, {1}, {3}` in agent 2's place gives the same
posteriors on the same data (`partitional_agent_same_disagreement`, the two auditors' probe
ported), and at world `0` agent 2's cell reaches world `2`, where agent 1's posterior is
`1/2 ≠ 1/4`, so the pair of posterior values is common knowledge nowhere on `C`
(`witness_posteriors_not_commonKnowledge`). That is the shape the lab's
`run2/brainstorm/tractable-wins.md` Candidate 1 pre-registered as its fake (ii) ("build a frame
where common knowledge of posteriors simply FAILS … and call it disagreement — that is not
Aumann-disagreement, it's no-common-knowledge"), and it is what the scout's scare quotes around
"sharing" (`run3/questions/scout-lean-scout.md` Q6(2): two agents "sharing" a common-knowledge
event) were pointing at. Graded N+ for what it shows (a computed disagreement on a proper event
that only one agent knows) and N− for modesty.

**Pushed further (repair round 2): transitivity cannot be dropped from the refutation.**
`nontransitive_disagreement_witness`: agent 2 reflexive and **not** transitive
(`K 0 = {0,1}, K 1 = {1,2}, K 2 = {1,2}, K 3 = {3}` — non-partitional, but outside the lab's
modest (S4) class, since it fails positive introspection), `C = {0,1,2}` closed under *both*
correspondences, agent 1's cell-posterior `1/3 = 𝔼_π(X | C)` and agent 2's `1/2` at every world
of `C`: agreeing to disagree on a genuinely common-knowledge event, with the posteriors constant
on it (so "agent 1 says `1/3` and agent 2 says `1/2`" is itself common knowledge there). This is
the regime of Geanakoplos ("Game theory without partitions", 1989, from memory), and it shows
`preorder_averaging` fails without transitivity: the common-knowledge disagreement the lab wanted
exists, but only by dropping positive introspection, not by modesty.

Pre-registered fakes (mandate; tractable-wins C1): `C = univ` — avoided (`C ≠ univ` compiled in
every instance); disagreement hypothesized — avoided (computed in every instance); non-common
prior — avoided (one `π`); **a no-common-knowledge frame called disagreement — not avoided by
round 0's witness**, which is exactly that shape, now said so in its name, grade and docstring.
Mathlib + `TtFiniteFrames.Corr` only (the mandate's added import edge, recorded in the report).
-/

namespace Cleanroom.Trust.TrustMerge

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Trust.TtFiniteFrames

noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]

/-- **The conditional expectation of `X` given an event** `S` under `π`, ratio form
`Σ_{w∈S} π_w X_w / π(S)` (`lit-ddb-frames`'s `mass`); Lean's `x / 0 = 0` is the junk value, which
every theorem below guards by positive mass.
Source: trust-lab-2-036 ("agent `i`'s posterior of `X`"); Aumann 1976
Kind: D
Fidelity: exact (guarded)
Hyps: n/a -/
def condE (π X : W → ℝ) (S : Finset W) : ℝ := (∑ w ∈ S, π w * X w) / mass π S

/-- **Self-evidence**: `C` is a union of `K`-cells — every cell at a world of `C` lies in `C`.
For a partitional `K` this is "`C` is a union of cells"; for a general `K` it is closure under
the correspondence.
Source: trust-lab-2-036 ("an event `C` that is a union of `E1`-cells and of `E2`-cells … a proper
self-evident sub-event")
Kind: D
Fidelity: exact
Hyps: n/a -/
def SelfEvident (K : Corr W) (C : Finset W) : Prop := ∀ w ∈ C, K w ⊆ C

omit [Fintype W] [DecidableEq W] in
/-- A constant posterior on a positive-mass event is the event's weighted sum.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_mul_eq_of_condE {π X : W → ℝ} {S : Finset W} {q : ℝ} (hpos : 0 < mass π S)
    (h : condE π X S = q) : ∑ w ∈ S, π w * X w = q * mass π S := by
  unfold condE at h
  rw [div_eq_iff hpos.ne'] at h
  exact h

/-- Summing over a self-evident event is summing over the cells it is made of (partitional `K`).
Source: none: infrastructure (`tt-finite-frames` `Partitional.sum_cells`, restricted to `C`)
Kind: L
Fidelity: n/a -/
theorem sum_selfEvident_cells {K : Corr W} (hK : Corr.Partitional K) {C : Finset W}
    (hC : SelfEvident K C) (g : W → ℝ) :
    ∑ w ∈ C, g w = ∑ c ∈ C.image K, ∑ w ∈ c, g w := by
  rw [← sum_fiberwise_of_maps_to (g := K) (t := C.image K)
    (fun w hw => mem_image_of_mem K hw)]
  apply sum_congr rfl
  intro c hc
  obtain ⟨v, hv, rfl⟩ := mem_image.1 hc
  apply sum_congr _ (fun _ _ => rfl)
  ext w
  simp only [mem_filter]
  constructor
  · rintro ⟨_, hw⟩
    rw [← hw]
    exact hK.1 w
  · intro hw
    exact ⟨hC v hv hw, hK.mem_iff_eq.1 hw⟩

/-- **Partition averaging**: over a self-evident event, a partitional agent whose cell-posterior
of `X` is the constant `q` at every world of the event has event-posterior `q`.
Source: trust-lab-2-036 ("finite Aumann via partition averaging per agent"); the idea from the
lab's `run2/lean/aumann-modesty.lean` `partition_averaging` (single-agent, `C = univ`, two
masks), generalized and re-proved
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem partition_averaging {K : Corr W} (hK : Corr.Partitional K) {π : W → ℝ}
    (hpos : ∀ w, 0 < π w) {C : Finset W} (hC : SelfEvident K C) (hne : C.Nonempty)
    {X : W → ℝ} {q : ℝ} (hq : ∀ w ∈ C, condE π X (K w) = q) : condE π X C = q := by
  have hnum : ∑ w ∈ C, π w * X w = q * mass π C := by
    rw [sum_selfEvident_cells hK hC (fun w => π w * X w)]
    rw [show mass π C = ∑ c ∈ C.image K, mass π c from by
      unfold mass
      exact sum_selfEvident_cells hK hC π]
    rw [mul_sum]
    apply sum_congr rfl
    intro c hc
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hc
    exact sum_mul_eq_of_condE (Corr.mass_pos_of_reflexive hpos hK.1 v) (hq v hv)
  have hmass : 0 < mass π C := by
    obtain ⟨v, hv⟩ := hne
    exact mass_pos_of_mem (fun w => (hpos w).le) hv (hpos v)
  unfold condE
  rw [hnum, mul_div_assoc, div_self hmass.ne', mul_one]

/-- **T9(1) (headline). Aumann 1976, instantiated:** two partitional agents with a common
full-support prior, an event `C` self-evident to both and nonempty, each agent's cell-posterior of
`X` constant on `C` — then the two constants agree and equal the event's posterior. `C ≠ univ` is
not needed by the proof; the concrete instance supplies a proper `C`.
Source: trust-lab-2-036 (1); Aumann, "Agreeing to disagree" (1976)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem aumann_two_agent {E1 E2 : Corr W} (h1 : Corr.Partitional E1) (h2 : Corr.Partitional E2)
    {π : W → ℝ} (hpos : ∀ w, 0 < π w) {C : Finset W} (hC1 : SelfEvident E1 C)
    (hC2 : SelfEvident E2 C) (hne : C.Nonempty) {X : W → ℝ} {q1 q2 : ℝ}
    (hq1 : ∀ w ∈ C, condE π X (E1 w) = q1) (hq2 : ∀ w ∈ C, condE π X (E2 w) = q2) :
    q1 = q2 ∧ q1 = condE π X C := by
  have e1 := partition_averaging h1 hpos hC1 hne hq1
  have e2 := partition_averaging h2 hpos hC2 hne hq2
  exact ⟨e1.symm.trans e2, e1.symm⟩

/-! ## Agreement is forced for every reflexive transitive correspondence (F-T9, proved) -/

omit [Fintype W] [DecidableEq W] in
/-- The centred weighted sum over a positive-mass cell with posterior `q` is zero:
`Σ_{v∈S} π v (X v − q) = 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_centred_eq_zero_of_condE {π X : W → ℝ} {S : Finset W} {q : ℝ}
    (hpos : 0 < mass π S) (h : condE π X S = q) : ∑ w ∈ S, π w * (X w - q) = 0 := by
  have h1 := sum_mul_eq_of_condE hpos h
  have h2 : ∑ w ∈ S, π w * (X w - q) = ∑ w ∈ S, π w * X w - q * mass π S := by
    unfold mass
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl (fun w _ => by ring)
  rw [h2, h1]
  ring

omit [Fintype W] in
/-- **Preorder averaging, the engine** (F-T9 proved): for a correspondence `K` that is reflexive
and transitive *on* `C` (`w ∈ K w` and `v ∈ K w → K v ⊆ K w` for `w ∈ C`), with `C` closed
under `K` and the cell sums `Σ_{K w} Y = 0` at every `w ∈ C`, the sum over `C` is `0`. Induction
on `|C|`: remove a cell `K w₀` of least cardinality — it is an equivalence class (each of its
members has the same cell, by transitivity and minimality), and every cell `K v`, `v ∈ C`, either
misses it or contains it (a common point `u` has `K u = K w₀ ⊆ K v`) — so `C \ K w₀` with the
trimmed cells `K v \ K w₀` satisfies the same hypotheses; the trimmed cell sums are `0 − 0`.
Source: trust-lab-2-036 (2) (what the search for the witness showed); F-T9's sketch, with the
Möbius inversion replaced by this induction
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem sum_centred_eq_zero_of_cells (Y : W → ℝ) :
    ∀ (C : Finset W) (K : Corr W), (∀ w ∈ C, w ∈ K w) → (∀ w ∈ C, ∀ v ∈ K w, K v ⊆ K w) →
      (∀ w ∈ C, K w ⊆ C) → (∀ w ∈ C, ∑ v ∈ K w, Y v = 0) → ∑ v ∈ C, Y v = 0 := by
  intro C
  induction C using Finset.strongInduction with
  | H C ih =>
    intro K hrefl htrans hclosed hzero
    rcases C.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨w₀, hw₀, hmin⟩ := C.exists_min_image (fun w => (K w).card) hne
    -- the least cell is an equivalence class
    have hclass : ∀ v ∈ K w₀, K v = K w₀ := fun v hv =>
      Finset.eq_of_subset_of_card_le (htrans w₀ hw₀ v hv) (hmin v (hclosed w₀ hw₀ hv))
    -- every cell of `C` misses it or contains it
    have hdich : ∀ v ∈ C, Disjoint (K v) (K w₀) ∨ K w₀ ⊆ K v := by
      intro v hv
      by_cases h : Disjoint (K v) (K w₀)
      · exact Or.inl h
      · obtain ⟨u, hu⟩ := Finset.not_disjoint_iff.1 h
        right
        rw [← hclass u hu.2]
        exact htrans v hv u hu.1
    have hsub : K w₀ ⊆ C := hclosed w₀ hw₀
    have hlt : C \ K w₀ ⊂ C := Finset.sdiff_ssubset hsub ⟨w₀, hrefl w₀ hw₀⟩
    have ih' : ∑ v ∈ C \ K w₀, Y v = 0 := by
      refine ih (C \ K w₀) hlt (fun v => K v \ K w₀) ?_ ?_ ?_ ?_
      · intro v hv
        rw [Finset.mem_sdiff] at hv ⊢
        exact ⟨hrefl v hv.1, hv.2⟩
      · intro v hv u hu
        rw [Finset.mem_sdiff] at hv hu
        exact Finset.sdiff_subset_sdiff (htrans v hv.1 u hu.1) (Finset.Subset.refl _)
      · intro v hv
        rw [Finset.mem_sdiff] at hv
        exact Finset.sdiff_subset_sdiff (hclosed v hv.1) (Finset.Subset.refl _)
      · intro v hv
        rw [Finset.mem_sdiff] at hv
        rcases hdich v hv.1 with hd | hd
        · rw [Finset.sdiff_eq_self_of_disjoint hd]
          exact hzero v hv.1
        · have h := Finset.sum_sdiff (f := Y) hd
          rw [hzero v hv.1, hzero w₀ hw₀] at h
          linarith
    have h := Finset.sum_sdiff (f := Y) hsub
    rw [ih', hzero w₀ hw₀] at h
    linarith

/-- **Preorder averaging** (F-T9, proved): over an event closed under a reflexive transitive
correspondence `K`, an agent whose `K`-cell-posterior of `X` is the constant `q` at every world of
the event has event-posterior `q`. `partition_averaging` without partitionality: the cells are
the principal down-sets of the preorder `v ≤ w :⟺ v ∈ K w`, and the engine above handles them.
Transitivity is needed: `nontransitive_disagreement_witness` has a reflexive non-transitive `K`,
a `K`-closed `C` and constant cell-posteriors `1/2` with `C`-posterior `1/3`.
Source: trust-lab-2-036 (2); F-T9 (the conjecture of round 0, now a theorem); audit r1 B3;
literature (from memory, audit r2 adversarial N11): Samet, "Ignoring ignorance and agreeing to
disagree", *J. Econ. Theory* 52 (1990) — the agreement theorem for reflexive transitive
(non-partitional) information; this is its finite instance, not a discovery
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem preorder_averaging {K : Corr W} (hrefl : Corr.Reflexive K) (htrans : Corr.Transitive K)
    {π : W → ℝ} (hpos : ∀ w, 0 < π w) {C : Finset W} (hC : SelfEvident K C) (hne : C.Nonempty)
    {X : W → ℝ} {q : ℝ} (hq : ∀ w ∈ C, condE π X (K w) = q) : condE π X C = q := by
  have hzero : ∑ v ∈ C, π v * (X v - q) = 0 :=
    sum_centred_eq_zero_of_cells (fun v => π v * (X v - q)) C K (fun w _ => hrefl w)
      (fun w _ v hv => htrans w v hv) hC
      (fun w hw => sum_centred_eq_zero_of_condE (Corr.mass_pos_of_reflexive hpos hrefl w) (hq w hw))
  have hmass : 0 < mass π C := by
    obtain ⟨v, hv⟩ := hne
    exact mass_pos_of_mem (fun w => (hpos w).le) hv (hpos v)
  have h2 : ∑ v ∈ C, π v * (X v - q) = ∑ w ∈ C, π w * X w - q * mass π C := by
    unfold mass
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl (fun w _ => by ring)
  unfold condE
  rw [div_eq_iff hmass.ne']
  linarith

/-- **Aumann for reflexive transitive agents** (the generalization of `aumann_two_agent`): two
agents whose correspondences are reflexive and transitive — partitional or not — with a common
full-support prior, an event closed under both and nonempty, constant cell-posteriors on it:
the constants agree and equal the event's posterior. Modesty (a non-partitional correspondence)
buys no disagreement on a common-knowledge event; dropping transitivity does
(`nontransitive_disagreement_witness`). Also refutes tractable-wins Candidate 2's bracket
"agreement ⟺ (no modesty), on the finite frame": agreement holds *with* modesty on a closed event.
Source: trust-lab-2-036 (2); F-T9; audit r1 B3; Samet 1990 (from memory, see
`preorder_averaging`)
Kind: P
Fidelity: stronger: `aumann_two_agent` without partitionality
Hyps: (a) none -/
theorem aumann_two_agent_preorder {E1 E2 : Corr W} (h1r : Corr.Reflexive E1)
    (h1t : Corr.Transitive E1) (h2r : Corr.Reflexive E2) (h2t : Corr.Transitive E2)
    {π : W → ℝ} (hpos : ∀ w, 0 < π w) {C : Finset W} (hC1 : SelfEvident E1 C)
    (hC2 : SelfEvident E2 C) (hne : C.Nonempty) {X : W → ℝ} {q1 q2 : ℝ}
    (hq1 : ∀ w ∈ C, condE π X (E1 w) = q1) (hq2 : ∀ w ∈ C, condE π X (E2 w) = q2) :
    q1 = q2 ∧ q1 = condE π X C := by
  have e1 := preorder_averaging h1r h1t hpos hC1 hne hq1
  have e2 := preorder_averaging h2r h2t hpos hC2 hne hq2
  exact ⟨e1.symm.trans e2, e1.symm⟩

/-- **T9(2), the closed reading, refuted:** trust-lab-2-036 (2) asks for a partitional agent 1
and a reflexive transitive non-partitional agent 2 sharing a common-knowledge event `C` on which
their constant cell-posteriors differ. If "common knowledge" means `C` closed under *both*
correspondences, no such data exist: the posteriors agree. The witness
`noCommonKnowledge_disagreement_witness` exists only because its `C₄` is not closed under `K₄`
(and a partitional agent 2 does the same there); with transitivity dropped the closed form is
satisfiable (`nontransitive_disagreement_witness`).
Source: trust-lab-2-036 (2) ("exhibit `C` covered by both agents' cells with cell-posteriors
constant `q1` and `q2 ≠ q1`"); F-T9; audit r1 B3; audit r2 B1
Kind: P
Fidelity: exact (the closed reading of the source's (2); its negation is the theorem)
Hyps: (a) none -/
theorem modest_disagreement_closed_refuted {E1 K : Corr W} (h1 : Corr.Partitional E1)
    (hKr : Corr.Reflexive K) (hKt : Corr.Transitive K) {π : W → ℝ} (hpos : ∀ w, 0 < π w)
    {C : Finset W} (hC1 : SelfEvident E1 C) (hCK : SelfEvident K C) (hne : C.Nonempty)
    {X : W → ℝ} {q1 q2 : ℝ} (hq1 : ∀ w ∈ C, condE π X (E1 w) = q1)
    (hq2 : ∀ w ∈ C, condE π X (K w) = q2) : q1 = q2 :=
  (aumann_two_agent_preorder h1.1 h1.transitive hKr hKt hpos hC1 hCK hne hq1 hq2).1

/-! ## The concrete proper instance (five worlds, two partitions) -/

/-- The uniform prior on five worlds.
Source: trust-lab-2-036 (1)
Kind: D
Fidelity: n/a -/
def π₅ : Fin 5 → ℝ := fun _ => 1 / 5

/-- Agent 1's partition: cells `{0,1}`, `{2,3}`, `{4}`.
Source: trust-lab-2-036 (1)
Kind: D
Fidelity: n/a -/
def E₁₅ : Corr (Fin 5) := Corr.ofMap ![0, 0, 1, 1, 2]

/-- Agent 2's partition: cells `{0,2}`, `{1,3}`, `{4}`.
Source: trust-lab-2-036 (1)
Kind: D
Fidelity: n/a -/
def E₂₅ : Corr (Fin 5) := Corr.ofMap ![0, 1, 0, 1, 2]

/-- The proper common-knowledge event `{0,1,2,3}` (a union of both agents' cells, not everything).
Source: trust-lab-2-036 (1) ("a proper self-evident sub-event — fixing run 2's whole-space
vacuity")
Kind: D
Fidelity: n/a -/
def C₅ : Finset (Fin 5) := {0, 1, 2, 3}

/-- The random variable `(1, 0, 0, 1, 0)`: non-constant on `C₅`.
Source: trust-lab-2-036 (1)
Kind: D
Fidelity: n/a -/
def X₅ : Fin 5 → ℝ := fun w => if w = 0 ∨ w = 3 then 1 else 0

/-- **T9(1), instance (N+)**: both partitions, the proper event (`C ≠ univ`, nonempty, self-evident
to both — compiled), cell-posteriors `1/2` for both agents on `C` (computed), hence agreement at
`1/2 = 𝔼_π(X | C)`.
Source: trust-lab-2-036 (1); mandate T9(1)
Kind: N+
Fidelity: exact
Hyps: n/a -/
theorem aumann_two_agent_example :
    Corr.Partitional E₁₅ ∧ Corr.Partitional E₂₅ ∧ C₅ ≠ univ ∧ C₅.Nonempty ∧
      SelfEvident E₁₅ C₅ ∧ SelfEvident E₂₅ C₅ ∧
      (∀ w ∈ C₅, condE π₅ X₅ (E₁₅ w) = 1 / 2) ∧ (∀ w ∈ C₅, condE π₅ X₅ (E₂₅ w) = 1 / 2) ∧
      condE π₅ X₅ C₅ = 1 / 2 := by
  refine ⟨Corr.ofMap_partitional _, Corr.ofMap_partitional _, by decide, ⟨0, by decide⟩,
    by unfold SelfEvident; decide, by unfold SelfEvident; decide, ?_, ?_, ?_⟩
  · intro w hw
    simp only [C₅, mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · rw [show E₁₅ 0 = {0, 1} from by decide]
      simp (config := { decide := true }) [condE, mass, X₅, π₅, Finset.sum_insert,
        Finset.card_insert_of_notMem] <;> norm_num
    · rw [show E₁₅ 1 = {0, 1} from by decide]
      simp (config := { decide := true }) [condE, mass, X₅, π₅, Finset.sum_insert,
        Finset.card_insert_of_notMem] <;> norm_num
    · rw [show E₁₅ 2 = {2, 3} from by decide]
      simp (config := { decide := true }) [condE, mass, X₅, π₅, Finset.sum_insert,
        Finset.card_insert_of_notMem] <;> norm_num
    · rw [show E₁₅ 3 = {2, 3} from by decide]
      simp (config := { decide := true }) [condE, mass, X₅, π₅, Finset.sum_insert,
        Finset.card_insert_of_notMem] <;> norm_num
  · intro w hw
    simp only [C₅, mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · rw [show E₂₅ 0 = {0, 2} from by decide]
      simp (config := { decide := true }) [condE, mass, X₅, π₅, Finset.sum_insert,
        Finset.card_insert_of_notMem] <;> norm_num
    · rw [show E₂₅ 1 = {1, 3} from by decide]
      simp (config := { decide := true }) [condE, mass, X₅, π₅, Finset.sum_insert,
        Finset.card_insert_of_notMem] <;> norm_num
    · rw [show E₂₅ 2 = {0, 2} from by decide]
      simp (config := { decide := true }) [condE, mass, X₅, π₅, Finset.sum_insert,
        Finset.card_insert_of_notMem] <;> norm_num
    · rw [show E₂₅ 3 = {1, 3} from by decide]
      simp (config := { decide := true }) [condE, mass, X₅, π₅, Finset.sum_insert,
        Finset.card_insert_of_notMem] <;> norm_num
  · simp (config := { decide := true }) [condE, mass, X₅, π₅, C₅, Finset.sum_insert,
      Finset.card_insert_of_notMem] <;> norm_num

/-! ## The surviving instance: disagreement without common knowledge (four worlds) -/

/-- The uniform prior on four worlds.
Source: trust-lab-2-036 (2)
Kind: D
Fidelity: n/a -/
def π₄ : Fin 4 → ℝ := fun _ => 1 / 4

/-- Agent 1's partition: cells `{0,1}`, `{2,3}`.
Source: trust-lab-2-036 (2)
Kind: D
Fidelity: n/a -/
def E₁₄ : Corr (Fin 4) := Corr.ofMap ![0, 0, 1, 1]

/-- Agent 2's reflexive, transitive, non-partitional correspondence:
`K 0 = {0,1,2}`, `K 1 = {1}`, `K 2 = {2}`, `K 3 = {3}`.
Source: trust-lab-2-036 (2) ("a reflexive-transitive non-partitional correspondence")
Kind: D
Fidelity: n/a -/
def K₄ : Corr (Fin 4) := ![{0, 1, 2}, {1}, {2}, {3}]

/-- The event `{0,1}`: a cell of agent 1, *not* closed under agent 2's correspondence.
Source: trust-lab-2-036 (2)
Kind: D
Fidelity: n/a -/
def C₄ : Finset (Fin 4) := {0, 1}

/-- The random variable `(0, 1/2, 1, 0)`.
Source: trust-lab-2-036 (2)
Kind: D
Fidelity: n/a -/
def X₄ : Fin 4 → ℝ := fun w => if w = 1 then 1 / 2 else if w = 2 then 1 else 0

/-- **T9(2), the surviving instance — disagreement without common knowledge (N+ for that; N− for
modesty: the non-partitional structure is inert).** Agent 2's correspondence is reflexive,
transitive and not partitional; `C₄ = {0,1}` is a proper nonempty event, self-evident to agent 1
and **not** to agent 2 (`K 0 ⊄ C₄`); on `C₄` agent 1's cell-posterior is `1/4` and agent 2's is
`1/2` at both worlds — computed from `π, E1, K, X`. This is *not* a modest disagreement: the
partition `{0,2}, {1}, {3}` in agent 2's place gives the same posteriors on the same data
(`partitional_agent_same_disagreement`); the disagreement is produced by `C₄` not being closed on
agent 2's side, and the pair of posterior values is common knowledge nowhere on `C₄`
(`witness_posteriors_not_commonKnowledge`). It is the no-common-knowledge shape that
tractable-wins Candidate 1 pre-registered as fake (ii), kept to show what fails: the closed form
with a transitive agent 2 is unsatisfiable (`modest_disagreement_closed_refuted`), and the closed
form with transitivity dropped is `nontransitive_disagreement_witness`. Round 0 named this
`modest_disagreement_witness` and graded it N+ for modesty; renamed and regraded in repair round
2 (audit r2 B1, both lenses) — the mandate's name is dropped because it oversells ([[STANDARDS]]
§3).
Source: trust-lab-2-036 (2); `run2/brainstorm/tractable-wins.md` Candidate 1, pre-registered
fake (ii); `run3/questions/scout-lean-scout.md` Q6(2) (the scare-quoted "sharing"); mandate
T9(2); audit r1 B3; audit r2 B1
Kind: N+ (disagreement without common knowledge) / N− (modesty — inert)
Fidelity: weaker: the event is not closed under agent 2's correspondence (known to agent 1
only); the source's closed form is unsatisfiable with a transitive agent 2
Hyps: n/a -/
theorem noCommonKnowledge_disagreement_witness :
    Corr.Reflexive K₄ ∧ Corr.Transitive K₄ ∧ ¬ Corr.Partitional K₄ ∧
      Corr.Partitional E₁₄ ∧ C₄ ≠ univ ∧ C₄.Nonempty ∧
      SelfEvident E₁₄ C₄ ∧ ¬ SelfEvident K₄ C₄ ∧
      (∀ w ∈ C₄, condE π₄ X₄ (E₁₄ w) = 1 / 4) ∧ (∀ w ∈ C₄, condE π₄ X₄ (K₄ w) = 1 / 2) ∧
      (1 / 4 : ℝ) ≠ 1 / 2 := by
  refine ⟨by unfold Corr.Reflexive; decide, by unfold Corr.Transitive; decide,
    by unfold Corr.Partitional Corr.Reflexive; decide, Corr.ofMap_partitional _, by decide,
    ⟨0, by decide⟩, by unfold SelfEvident; decide, by unfold SelfEvident; decide, ?_, ?_,
    by norm_num⟩
  · intro w hw
    simp only [C₄, mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl
    · rw [show E₁₄ 0 = {0, 1} from by decide]
      simp (config := { decide := true }) [condE, mass, X₄, π₄, Finset.sum_insert,
        Finset.card_insert_of_notMem] <;> norm_num
    · rw [show E₁₄ 1 = {0, 1} from by decide]
      simp (config := { decide := true }) [condE, mass, X₄, π₄, Finset.sum_insert,
        Finset.card_insert_of_notMem] <;> norm_num
  · intro w hw
    simp only [C₄, mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl
    · rw [show K₄ 0 = {0, 1, 2} from rfl]
      simp (config := { decide := true }) [condE, mass, X₄, π₄, Finset.sum_insert,
        Finset.card_insert_of_notMem] <;> norm_num
    · rw [show K₄ 1 = {1} from rfl]
      simp (config := { decide := true }) [condE, mass, X₄, π₄,
        Finset.card_insert_of_notMem] <;> norm_num

/-! ## Modesty is inert in that instance (audit r2 B1, the two auditors' probe ported) -/

/-- Agent 2 made partitional on the same frame: cells `{0,2}`, `{1}`, `{3}`.
Source: audit r2 B1 (probes `ModestyInert.lean`, `PartitionalAgentSameDisagreement.lean`)
Kind: D
Fidelity: n/a -/
def E₂₄' : Corr (Fin 4) := Corr.ofMap ![0, 1, 0, 2]

/-- **A partitional agent 2 reproduces the witness's disagreement on the same data:** with `π₄`,
`E₁₄`, `C₄`, `X₄` unchanged and the partition `E₂₄'` in `K₄`'s place, `C₄` is still self-evident
to agent 1 only and the cell-posteriors are still `1/4` vs `1/2`. So the non-partitional
structure of `K₄` does no work in `noCommonKnowledge_disagreement_witness`; what produces the
disagreement is the event not being common knowledge.
Source: audit r2 B1 (both lenses; their probes, ported)
Kind: N− (the witness's modesty shown idle)
Fidelity: exact
Hyps: n/a -/
theorem partitional_agent_same_disagreement :
    Corr.Partitional E₂₄' ∧ SelfEvident E₁₄ C₄ ∧ ¬ SelfEvident E₂₄' C₄ ∧
      (∀ w ∈ C₄, condE π₄ X₄ (E₁₄ w) = 1 / 4) ∧ (∀ w ∈ C₄, condE π₄ X₄ (E₂₄' w) = 1 / 2) := by
  refine ⟨Corr.ofMap_partitional _, by unfold SelfEvident; decide,
    by unfold SelfEvident E₂₄'; decide, ?_, ?_⟩
  · intro w hw
    simp only [C₄, mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl
    · rw [show E₁₄ 0 = {0, 1} from by decide]
      simp (config := { decide := true }) [condE, mass, X₄, π₄, Finset.sum_insert,
        Finset.card_insert_of_notMem] <;> norm_num
    · rw [show E₁₄ 1 = {0, 1} from by decide]
      simp (config := { decide := true }) [condE, mass, X₄, π₄, Finset.sum_insert,
        Finset.card_insert_of_notMem] <;> norm_num
  · intro w hw
    simp only [C₄, mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl
    · rw [show E₂₄' 0 = {0, 2} from by decide]
      simp (config := { decide := true }) [condE, mass, X₄, π₄, Finset.sum_insert,
        Finset.card_insert_of_notMem] <;> norm_num
    · rw [show E₂₄' 1 = {1} from by decide]
      simp (config := { decide := true }) [condE, mass, X₄, π₄,
        Finset.card_insert_of_notMem] <;> norm_num

/-- **The witness's posteriors are common knowledge nowhere on `C₄`:** at world `0 ∈ C₄` agent
2's cell `K₄ 0 = {0,1,2}` contains world `2`, where agent 1's cell-posterior is `1/2 ≠ 1/4`, so
"agent 1's posterior is `1/4`" is not known to agent 2 at `0` — tractable-wins Candidate 1's
fake (ii), the no-common-knowledge shape, is what the witness is.
Source: audit r2 B1 (fidelity probe `ModestyInert.lean`, ported); tractable-wins C1 fake (ii)
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem witness_posteriors_not_commonKnowledge :
    (2 : Fin 4) ∈ K₄ 0 ∧ condE π₄ X₄ (E₁₄ 2) = 1 / 2 ∧ (1 / 2 : ℝ) ≠ 1 / 4 := by
  refine ⟨by decide, ?_, by norm_num⟩
  rw [show E₁₄ 2 = {2, 3} from by decide]
  simp (config := { decide := true }) [condE, mass, X₄, π₄, Finset.sum_insert,
    Finset.card_insert_of_notMem] <;> norm_num

/-! ## Pushed further: agreeing to disagree on a closed event needs only non-transitivity -/

/-- Agent 1's partition for the non-transitive frame: cells `{0,1,2}`, `{3}`.
Source: repair round 2 (the natural next question after `preorder_averaging`)
Kind: D
Fidelity: n/a -/
def E₁ₜ : Corr (Fin 4) := Corr.ofMap ![0, 0, 0, 1]

/-- Agent 2's reflexive, **non-transitive** correspondence:
`K 0 = {0,1}`, `K 1 = {1,2}`, `K 2 = {1,2}`, `K 3 = {3}` (`1 ∈ K 0` but `K 1 ⊄ K 0`).
Non-partitional, but not S4: it fails positive introspection, so it is outside the lab's
"modest" class.
Source: repair round 2; Geanakoplos, "Game theory without partitions" (1989; from memory)
Kind: D
Fidelity: n/a -/
def Kₜ : Corr (Fin 4) := ![{0, 1}, {1, 2}, {1, 2}, {3}]

/-- The event `{0,1,2}`: a cell of agent 1 and closed under `Kₜ` — common knowledge to both.
Source: repair round 2
Kind: D
Fidelity: n/a -/
def Cₜ : Finset (Fin 4) := {0, 1, 2}

/-- The random variable `(0, 1, 0, 0)`.
Source: repair round 2
Kind: D
Fidelity: n/a -/
def Xₜ : Fin 4 → ℝ := fun w => if w = 1 then 1 else 0

/-- **Agreeing to disagree on a common-knowledge event, with transitivity dropped (N+):** agent 1
partitional, agent 2 reflexive and **not** transitive, uniform prior, `Cₜ = {0,1,2}` proper,
nonempty and closed under *both* correspondences; agent 1's cell-posterior is `1/3` and agent 2's
is `1/2` at every world of `Cₜ`, and `𝔼_π(X | Cₜ) = 1/3` — all computed. So the event "agent 1
says `1/3` and agent 2 says `1/2`" contains `Cₜ` and is common knowledge at every world of it,
and the agents disagree there: the common-knowledge disagreement that tractable-wins Candidate 1
asked for, obtained not by modesty (which `modest_disagreement_closed_refuted` rules out) but by
dropping positive introspection; and a direct demonstration that `preorder_averaging` needs its
transitivity hypothesis (agent 2's cells all have posterior `1/2`, the event has `1/3`).
Source: trust-lab-2-036 (2) with "transitive" dropped; tractable-wins Candidate 1 (its (i)+(ii)
reading); Geanakoplos 1989 (from memory); repair round 2
Kind: N+
Fidelity: variant: the source's (2) with transitivity dropped (reflexive only); the closed
(common-knowledge) reading, which with transitivity is refuted
Hyps: n/a -/
theorem nontransitive_disagreement_witness :
    Corr.Reflexive Kₜ ∧ ¬ Corr.Transitive Kₜ ∧ Corr.Partitional E₁ₜ ∧
      Cₜ ≠ univ ∧ Cₜ.Nonempty ∧ SelfEvident E₁ₜ Cₜ ∧ SelfEvident Kₜ Cₜ ∧
      (∀ w ∈ Cₜ, condE π₄ Xₜ (E₁ₜ w) = 1 / 3) ∧ (∀ w ∈ Cₜ, condE π₄ Xₜ (Kₜ w) = 1 / 2) ∧
      condE π₄ Xₜ Cₜ = 1 / 3 ∧ (1 / 3 : ℝ) ≠ 1 / 2 := by
  refine ⟨by unfold Corr.Reflexive; decide, by unfold Corr.Transitive; decide,
    Corr.ofMap_partitional _, by decide, ⟨0, by decide⟩, by unfold SelfEvident; decide,
    by unfold SelfEvident; decide, ?_, ?_, ?_, by norm_num⟩
  · intro w hw
    simp only [Cₜ, mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · rw [show E₁ₜ 0 = {0, 1, 2} from by decide]
      simp (config := { decide := true }) [condE, mass, Xₜ, π₄, Finset.sum_insert,
        Finset.card_insert_of_notMem] <;> norm_num
    · rw [show E₁ₜ 1 = {0, 1, 2} from by decide]
      simp (config := { decide := true }) [condE, mass, Xₜ, π₄, Finset.sum_insert,
        Finset.card_insert_of_notMem] <;> norm_num
    · rw [show E₁ₜ 2 = {0, 1, 2} from by decide]
      simp (config := { decide := true }) [condE, mass, Xₜ, π₄, Finset.sum_insert,
        Finset.card_insert_of_notMem] <;> norm_num
  · intro w hw
    simp only [Cₜ, mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · rw [show Kₜ 0 = {0, 1} from rfl]
      simp (config := { decide := true }) [condE, mass, Xₜ, π₄, Finset.sum_insert,
        Finset.card_insert_of_notMem] <;> norm_num
    · rw [show Kₜ 1 = {1, 2} from rfl]
      simp (config := { decide := true }) [condE, mass, Xₜ, π₄, Finset.sum_insert,
        Finset.card_insert_of_notMem] <;> norm_num
    · rw [show Kₜ 2 = {1, 2} from rfl]
      simp (config := { decide := true }) [condE, mass, Xₜ, π₄, Finset.sum_insert,
        Finset.card_insert_of_notMem] <;> norm_num
  · simp (config := { decide := true }) [condE, mass, Xₜ, π₄, Cₜ, Finset.sum_insert,
      Finset.card_insert_of_notMem] <;> norm_num

end

end Cleanroom.Trust.TrustMerge
