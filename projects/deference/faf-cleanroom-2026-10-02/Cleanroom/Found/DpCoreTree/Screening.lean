import Cleanroom.Found.DpCoreTree.NodeSums

/-!
# Lemma 3′: screening at a recorded point

T6 of [[dp-core-tree-mandate]] (dp-sl-010, dp-core-034; `sl-defensible-claims.md` S4).

**Lemma 3′** (`screening_recorded`): if `B` records at `d` for `C` (Definition 7) and `X` is
pre-query for `d` (every `d`-node met on a positive `O_d`-run decides `X`), then for every
action `a`
`ν(X ∩ a ∩ O_d) · ν(O_d) = ν(X ∩ O_d) · ν(a ∩ O_d)` — the act-conditional of `X` given `O_d` is
flat, for every procedure, with no hypothesis on post-query chance. Stated multiplicatively (no
junk division); the conditional form `ν(X ∣ a ∩ O_d) = ν(X ∣ O_d)` is the corollary
`screening_recorded_div` under the stated positivity.

Proof. Recording makes the positive `O_d`-runs pass exactly one `d`-node `q`, and makes
"`λ(ℓ) ⊨ a`" the event "the path took edge `a` at `q`" (clauses 3–4). Grouping by `q`: the
positive `O_d`-mass below `q` taking edge `a` is `C(d)(a)` times the positive `O_d`-mass below
`q` (`mass_edge`, Definition 6's independent draw), and `X` is constant below `q` (pre-query).
So `ν(X ∩ a ∩ O) = C(d)(a) ∑_q x_q W_q`, `ν(a ∩ O) = C(d)(a) ∑_q W_q`, `ν(X ∩ O) = ∑_q x_q W_q`,
`ν(O) = ∑_q W_q`, and the products agree. The independence of the draw from the path is *derived*
(`mass_edge`), not assumed.

**SSC form** (`screening_ssc_of_hStar`): under `H*` the same identity holds with `occ(d)` in
place of the `O_d`-runs (they coincide a.s.). Under `RecordsFor` alone it is **refuted**
(`Screening.lean`'s companion `ScreeningWitness.lean`: the mugging `B₁` at `C(d) = ½`).

**Lemma 3 as printed** (last section; repair round 1): its first clause read per node is empty
(`decidedAt_edge_identity`, true of any weighting — this replaces round 1's `screening_at_node`,
which the adversarial audit found vacuous); read on `occ(d)` it is the run-level theorem
`screening_draw`: with at most one `d`-node per positive run and `X` decided at every `d`-node,
`μ(X ∩ drew_a) · μ(occ) = μ(X ∩ occ) · μ(drew_a)` — no recording needed, because the draw's
conditional law is `C(d)` at every node (`mass_edge`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree

open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] [DecidableEq ι]
  [DecidableEq Ω] [Fintype Ω]

namespace Tree

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)

/-- `ν` as a sum over the positive-mass leaves.
Source: none: infrastructure
Kind: L -/
theorem nu_eq_sum_pos (C : Proc ι acts K) (B : Tree Ω ι acts K) (Y : Finset Ω) :
    nu C B Y = ∑ ℓ, if 0 < leafLaw C B ℓ ∧ world B ℓ ∈ Y then leafLaw C B ℓ else 0 := by
  rw [nu_eq_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rcases (leafLaw_nonneg C B ℓ).lt_or_eq with h | h
  · simp [h]
  · rw [← h]; simp

/-! ### Per-node quantities -/

/-- The positive `O_d`-mass below `q`: `∑_{ℓ below q, μ(ℓ) > 0, λ(ℓ) ⊨ O_d} μ(ℓ)`.
Source: none: infrastructure (the `R_q`-like weight of the proof of Lemma 3′)
Kind: D -/
def obsMassBelow (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (q : B.DecNode) : K :=
  ∑ ℓ, if 0 < leafLaw C B ℓ ∧ world B ℓ ∈ obs d ∧ (edgeOf B q ℓ).isSome then leafLaw C B ℓ else 0

/-- The indicator that every leaf below `q` lies in `X`.
Source: none: infrastructure
Kind: D -/
def belowInd (B : Tree Ω ι acts K) (q : B.DecNode) (X : Finset Ω) : K :=
  if ∀ ℓ ∈ leavesBelow B q, world B ℓ ∈ X then 1 else 0

/-- A node is *active* if some positive `O_d`-run passes it.
Source: none: infrastructure
Kind: D -/
def ActiveNode (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (q : B.DecNode) : Prop :=
  ∃ ℓ, 0 < leafLaw C B ℓ ∧ world B ℓ ∈ obs d ∧ (edgeOf B q ℓ).isSome

/-- On an inactive node every positive-`O_d`-below-`q` sum vanishes.
Source: none: infrastructure
Kind: L -/
theorem sum_eq_zero_of_not_active {C : Proc ι acts K} {B : Tree Ω ι acts K} {d : ι}
    {q : B.DecNode} (h : ¬ ActiveNode obs C B d q) (P : B.Leaves → Prop) [DecidablePred P]
    (hP : ∀ ℓ, P ℓ → (edgeOf B q ℓ).isSome) :
    (∑ ℓ, if 0 < leafLaw C B ℓ ∧ world B ℓ ∈ obs d ∧ P ℓ then leafLaw C B ℓ else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro ℓ _
  rw [if_neg]
  rintro ⟨h1, h2, h3⟩
  exact h ⟨ℓ, h1, h2, hP ℓ h3⟩

/-- **Node edge mass**: at a `d`-node `q` that is subtree-veridical whenever active, the positive
`O_d`-mass below `q` taking edge `a` is `C(d)(a)` times the positive `O_d`-mass below `q`.
Source: [[decision-problems-v2]] §7.3 Lemma 3 proof ("Definition 6 samples the draw
independently of the path"), made node-local
Kind: P -/
theorem node_mass_edge (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (q : B.DecNode)
    (hq : pt B q = d) (hsv : ActiveNode obs C B d q → SubtreeVeridical obs B q) (a : acts d) :
    (∑ ℓ, if 0 < leafLaw C B ℓ ∧ world B ℓ ∈ obs d ∧ edgeS B q ℓ = some ⟨d, a⟩
        then leafLaw C B ℓ else 0) =
      (C d).w a * obsMassBelow obs C B d q := by
  subst hq
  by_cases hact : ActiveNode obs C B (pt B q) q
  · have hsv' := hsv hact
    unfold obsMassBelow
    have e1 : ∀ ℓ, (if 0 < leafLaw C B ℓ ∧ world B ℓ ∈ obs (pt B q) ∧
        edgeS B q ℓ = some ⟨pt B q, a⟩ then leafLaw C B ℓ else 0) =
        if edgeOf B q ℓ = some a then leafLaw C B ℓ else 0 := by
      intro ℓ
      simp only [edgeS_eq_some_iff]
      by_cases he : edgeOf B q ℓ = some a
      · rw [if_pos he]
        have hbelow : ℓ ∈ leavesBelow B q := by rw [mem_leavesBelow, he]; rfl
        have hO := hsv' ℓ hbelow
        rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hzero
        · rw [if_pos ⟨hpos, hO, he⟩]
        · rw [← hzero]; simp
      · rw [if_neg he, if_neg]; rintro ⟨-, -, h⟩; exact he h
    have e2 : ∀ ℓ, (if 0 < leafLaw C B ℓ ∧ world B ℓ ∈ obs (pt B q) ∧ (edgeOf B q ℓ).isSome
        then leafLaw C B ℓ else 0) =
        if (edgeOf B q ℓ).isSome then leafLaw C B ℓ else 0 := by
      intro ℓ
      by_cases he : (edgeOf B q ℓ).isSome
      · rw [if_pos he]
        have hO := hsv' ℓ ((mem_leavesBelow B q ℓ).mpr he)
        rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hzero
        · rw [if_pos ⟨hpos, hO, he⟩]
        · rw [← hzero]; simp
      · rw [if_neg he, if_neg]; rintro ⟨-, -, h⟩; exact he h
    simp only [e1, e2]
    exact mass_edge C B q a
  · rw [sum_eq_zero_of_not_active obs hact _ (fun ℓ h => isSome_of_edgeS B q ℓ h)]
    unfold obsMassBelow
    rw [sum_eq_zero_of_not_active obs hact _ (fun ℓ h => h), mul_zero]

/-- Inserting a pre-query event: on a `d`-node that is decided whenever active, the `X`-restricted
sums pick up the constant factor `belowInd q X`.
Source: none: infrastructure
Kind: L -/
theorem node_sum_inter_X (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (q : B.DecNode)
    (X : Finset Ω) (hdec : ActiveNode obs C B d q → DecidedAt B q X) (P : B.Leaves → Prop)
    [DecidablePred P] (hP : ∀ ℓ, P ℓ → (edgeOf B q ℓ).isSome) :
    (∑ ℓ, if 0 < leafLaw C B ℓ ∧ world B ℓ ∈ obs d ∧ world B ℓ ∈ X ∧ P ℓ
        then leafLaw C B ℓ else 0) =
      belowInd B q X *
        ∑ ℓ, if 0 < leafLaw C B ℓ ∧ world B ℓ ∈ obs d ∧ P ℓ then leafLaw C B ℓ else 0 := by
  by_cases hact : ActiveNode obs C B d q
  · rcases hdec hact with hin | hout
    · have hx : belowInd B q X = 1 := by
        unfold belowInd; rw [if_pos hin]
      rw [hx, one_mul]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      by_cases hc : 0 < leafLaw C B ℓ ∧ world B ℓ ∈ obs d ∧ P ℓ
      · rw [if_pos hc, if_pos ⟨hc.1, hc.2.1, hin ℓ ((mem_leavesBelow B q ℓ).mpr (hP ℓ hc.2.2)),
          hc.2.2⟩]
      · rw [if_neg hc, if_neg]; rintro ⟨h1, h2, -, h4⟩; exact hc ⟨h1, h2, h4⟩
    · have hx : belowInd B q X = 0 := by
        unfold belowInd
        rw [if_neg]
        intro hall
        -- an active node has a positive leaf below it, in `X` and not in `X`
        obtain ⟨ℓ₀, -, -, he⟩ := hact
        have hb := (mem_leavesBelow B q ℓ₀).mpr he
        exact hout ℓ₀ hb (hall ℓ₀ hb)
      rw [hx, zero_mul]
      apply Finset.sum_eq_zero
      intro ℓ _
      rw [if_neg]
      rintro ⟨-, -, h3, h4⟩
      exact hout ℓ ((mem_leavesBelow B q ℓ).mpr (hP ℓ h4)) h3
  · rw [sum_eq_zero_of_not_active obs hact _ (fun ℓ h => hP ℓ h), mul_zero]
    apply Finset.sum_eq_zero
    intro ℓ _
    rw [if_neg]
    rintro ⟨h1, h2, -, h4⟩
    exact hact ⟨ℓ, h1, h2, hP ℓ h4⟩

/-! ### Grouping positive `O_d`-runs by their unique `d`-node -/

/-- On a positive `O_d`-run of a recorded point, the `d`-nodes on the path form a singleton.
Source: [[decision-problems-v2]] Definition 7 ("passes exactly one `d`-node")
Kind: L -/
theorem dNodesOn_eq_singleton_of_recorded {C : Proc ι acts K} {B : Tree Ω ι acts K} {d : ι}
    (hrec : RecordsFor obs actEv C B d) {ℓ : B.Leaves} (hpos : 0 < leafLaw C B ℓ)
    (hobs : world B ℓ ∈ obs d) : ∃ q₀, dNodesOn B d ℓ = {q₀} := by
  have h := (hrec ℓ hpos hobs).1
  rw [count_eq_card_dNodesOn] at h
  exact Finset.card_eq_one.mp h

/-- A sum over the fiber of `d` whose terms vanish off the path collapses to the unique `d`-node
on the path.
Source: none: infrastructure
Kind: L -/
theorem sum_fiber_eq_of_singleton {B : Tree Ω ι acts K} {d : ι} {ℓ : B.Leaves} {q₀ : B.DecNode}
    (h : dNodesOn B d ℓ = {q₀}) (f : B.DecNode → K)
    (hf : ∀ q, ¬ (edgeOf B q ℓ).isSome → f q = 0) : ∑ q ∈ fiber B d, f q = f q₀ := by
  rw [← Finset.sum_filter_of_ne (p := fun q => (edgeOf B q ℓ).isSome)
    (fun q _ hq => by by_contra hc; exact hq (hf q hc))]
  rw [← dNodesOn_eq_filter_fiber, h, Finset.sum_singleton]

/-- On a positive `O_d`-run of a recorded point with unique `d`-node `q₀`: the leaf-world
satisfies the action event `a` iff the path took edge `a` at `q₀`.
Source: [[decision-problems-v2]] Definition 7 (clauses 3–4: "its instance is action-veridical;
and the leaf-world satisfies an action in `A_d` only if it is the one drawn there")
Kind: L -/
theorem actEv_iff_edgeS_of_recorded {C : Proc ι acts K} {B : Tree Ω ι acts K} {d : ι}
    (hrec : RecordsFor obs actEv C B d) {ℓ : B.Leaves} (hpos : 0 < leafLaw C B ℓ)
    (hobs : world B ℓ ∈ obs d) {q₀ : B.DecNode} (h : dNodesOn B d ℓ = {q₀}) (a : acts d) :
    world B ℓ ∈ actEv d a ↔ edgeS B q₀ ℓ = some ⟨d, a⟩ := by
  have hq₀ : q₀ ∈ dNodesOn B d ℓ := by rw [h]; exact Finset.mem_singleton_self _
  rw [mem_dNodesOn] at hq₀
  obtain ⟨hpt, he⟩ := hq₀
  subst hpt
  obtain ⟨a₀, ha₀⟩ := Option.isSome_iff_exists.mp he
  obtain ⟨-, hact, huniq⟩ := (hrec ℓ hpos hobs).2 q₀ rfl a₀ ha₀
  rw [edgeS_eq_some_iff, ha₀]
  constructor
  · intro hw
    rw [huniq a hw]
  · intro heq
    rw [Option.some.injEq] at heq
    rw [← heq]
    exact hact

/-! ### Lemma 3′ -/

/-- The `X ∩ a ∩ O_d`-mass grouped by `d`-node.
Source: none: infrastructure
Kind: L -/
theorem nu_inter_actEv_eq_sum_fiber {C : Proc ι acts K} {B : Tree Ω ι acts K} {d : ι}
    (hrec : RecordsFor obs actEv C B d) (X : Finset Ω) (a : acts d) :
    nu C B (X ∩ actEv d a ∩ obs d) =
      ∑ q ∈ fiber B d, ∑ ℓ, if 0 < leafLaw C B ℓ ∧ world B ℓ ∈ obs d ∧ world B ℓ ∈ X ∧
        edgeS B q ℓ = some ⟨d, a⟩ then leafLaw C B ℓ else 0 := by
  rw [nu_eq_sum_pos, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases hL : 0 < leafLaw C B ℓ ∧ world B ℓ ∈ obs d
  · obtain ⟨q₀, hq₀⟩ := dNodesOn_eq_singleton_of_recorded obs actEv hrec hL.1 hL.2
    rw [sum_fiber_eq_of_singleton hq₀ _ (fun q hq => by
      rw [if_neg]; rintro ⟨-, -, -, h⟩; exact hq (isSome_of_edgeS B q ℓ h))]
    simp only [← actEv_iff_edgeS_of_recorded obs actEv hrec hL.1 hL.2 hq₀ a, Finset.mem_inter]
    by_cases hx : world B ℓ ∈ X <;> by_cases ha : world B ℓ ∈ actEv d a <;> simp [hL, hx, ha]
  · rw [if_neg (fun h => hL ⟨h.1, (Finset.mem_inter.mp h.2).2⟩)]
    symm
    apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    rintro ⟨h1, h2, -, -⟩
    exact hL ⟨h1, h2⟩

/-- The `X ∩ O_d`-mass grouped by `d`-node.
Source: none: infrastructure
Kind: L -/
theorem nu_inter_obs_eq_sum_fiber {C : Proc ι acts K} {B : Tree Ω ι acts K} {d : ι}
    (hrec : RecordsFor obs actEv C B d) (X : Finset Ω) :
    nu C B (X ∩ obs d) =
      ∑ q ∈ fiber B d, ∑ ℓ, if 0 < leafLaw C B ℓ ∧ world B ℓ ∈ obs d ∧ world B ℓ ∈ X ∧
        (edgeOf B q ℓ).isSome then leafLaw C B ℓ else 0 := by
  rw [nu_eq_sum_pos, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases hL : 0 < leafLaw C B ℓ ∧ world B ℓ ∈ obs d
  · obtain ⟨q₀, hq₀⟩ := dNodesOn_eq_singleton_of_recorded obs actEv hrec hL.1 hL.2
    rw [sum_fiber_eq_of_singleton hq₀ _ (fun q hq => by
      rw [if_neg]; rintro ⟨-, -, -, h⟩; exact hq h)]
    have he : (edgeOf B q₀ ℓ).isSome := by
      have : q₀ ∈ dNodesOn B d ℓ := by rw [hq₀]; exact Finset.mem_singleton_self _
      exact ((mem_dNodesOn B d ℓ q₀).mp this).2
    simp only [Finset.mem_inter]
    by_cases hx : world B ℓ ∈ X <;> simp [hL, hx, he]
  · rw [if_neg (fun h => hL ⟨h.1, (Finset.mem_inter.mp h.2).2⟩)]
    symm
    apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    rintro ⟨h1, h2, -, -⟩
    exact hL ⟨h1, h2⟩

/-- **Lemma 3′ (screening at a recorded point)**: if `B` records at `d` for `C` and `X` is
pre-query for `d`, then `ν(X ∩ a ∩ O_d) · ν(O_d) = ν(X ∩ O_d) · ν(a ∩ O_d)` for every action `a`:
at a recorded point the act-conditionals of every pre-query event are flat, for every procedure,
with no hypothesis on post-query chance.
Source: `sl-workflow/notes/final/sl-defensible-claims.md` line 46 (S4 = Lemma 3′);
`sl-synthesis.md`; [[decision-problems-v2]] §7.3 Lemma 3 (the printed, under-hypothesised
form); mandate T6 (dp-sl-010)
Kind: P
Fidelity: exact (multiplicative form; the conditional form is `screening_recorded_div`)
Hyps: none — recording and pre-query are the theorem's own hypotheses (definitions of record),
and "the draw is independent of the path" is derived (`mass_edge`), not assumed -/
theorem screening_recorded {C : Proc ι acts K} {B : Tree Ω ι acts K} {d : ι}
    (hrec : RecordsFor obs actEv C B d) {X : Finset Ω} (hX : PreQuery obs C B d X)
    (a : acts d) :
    nu C B (X ∩ actEv d a ∩ obs d) * nu C B (obs d) =
      nu C B (X ∩ obs d) * nu C B (actEv d a ∩ obs d) := by
  -- the per-node facts supplied by recording and pre-query
  have hsv : ∀ q ∈ fiber B d, ActiveNode obs C B d q → SubtreeVeridical obs B q := by
    intro q hq ⟨ℓ, hpos, hobs, he⟩
    rw [fiber, Finset.mem_filter] at hq
    obtain ⟨a₀, ha₀⟩ := Option.isSome_iff_exists.mp he
    exact ((hrec ℓ hpos hobs).2 q hq.2 a₀ ha₀).1
  have hdec : ∀ q ∈ fiber B d, ActiveNode obs C B d q → DecidedAt B q X := by
    intro q hq ⟨ℓ, hpos, hobs, he⟩
    rw [fiber, Finset.mem_filter] at hq
    exact hX ℓ hpos hobs q hq.2 he
  -- the four masses as node sums
  have h1 : nu C B (X ∩ actEv d a ∩ obs d) =
      ∑ q ∈ fiber B d, belowInd B q X * ((C d).w a * obsMassBelow obs C B d q) := by
    rw [nu_inter_actEv_eq_sum_fiber obs actEv hrec X a]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [node_sum_inter_X obs C B d q X (hdec q hq) _ (fun ℓ h => isSome_of_edgeS B q ℓ h),
      node_mass_edge obs C B d q ((Finset.mem_filter.mp hq).2) (hsv q hq) a]
  have h2 : nu C B (obs d) = ∑ q ∈ fiber B d, obsMassBelow obs C B d q := by
    have := nu_inter_obs_eq_sum_fiber obs actEv hrec Finset.univ
    rw [Finset.univ_inter] at this
    rw [this]
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold obsMassBelow
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp only [Finset.mem_univ, true_and]
  have h3 : nu C B (X ∩ obs d) = ∑ q ∈ fiber B d, belowInd B q X * obsMassBelow obs C B d q := by
    rw [nu_inter_obs_eq_sum_fiber obs actEv hrec X]
    refine Finset.sum_congr rfl fun q hq => ?_
    exact node_sum_inter_X obs C B d q X (hdec q hq) _ (fun ℓ h => h)
  have h4 : nu C B (actEv d a ∩ obs d) =
      ∑ q ∈ fiber B d, (C d).w a * obsMassBelow obs C B d q := by
    have := nu_inter_actEv_eq_sum_fiber obs actEv hrec Finset.univ a
    rw [Finset.univ_inter] at this
    rw [this]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [← node_mass_edge obs C B d q ((Finset.mem_filter.mp hq).2) (hsv q hq) a]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp only [Finset.mem_univ, true_and]
  rw [h1, h2, h3, h4]
  simp only [mul_left_comm _ ((C d).w a), ← Finset.mul_sum]
  ring

/-- **Lemma 3′, conditional form**: under `ν(a ∩ O_d) > 0` and `ν(O_d) > 0`,
`ν(X ∩ a ∩ O_d) / ν(a ∩ O_d) = ν(X ∩ O_d) / ν(O_d)`.
Source: `sl-defensible-claims.md` S4
Kind: C -/
theorem screening_recorded_div {C : Proc ι acts K} {B : Tree Ω ι acts K} {d : ι}
    (hrec : RecordsFor obs actEv C B d) {X : Finset Ω} (hX : PreQuery obs C B d X)
    (a : acts d) (ha : 0 < nu C B (actEv d a ∩ obs d)) (hO : 0 < nu C B (obs d)) :
    nu C B (X ∩ actEv d a ∩ obs d) / nu C B (actEv d a ∩ obs d) =
      nu C B (X ∩ obs d) / nu C B (obs d) := by
  rw [div_eq_div_iff ha.ne' hO.ne']
  exact screening_recorded obs actEv hrec hX a

/-! ### The SSC (occurrence-conditioned) form under `H*` -/

/-- Under `H*`, the run-level mass of "`λ ⊨ Y` and consulted at `d`" is `ν(Y ∩ O_d)`.
Source: `sl-synthesis.md` line 20 (`H*`); [[decision-problems-v2]] Remark 3.4
Kind: L -/
theorem mass_worldEv_inter_occ_of_hStar {C : Proc ι acts K} {B : Tree Ω ι acts K} {d : ι}
    (h : HStar obs actEv C B d) (Y : Finset Ω) :
    mass C B (worldEv B Y ∩ occ d B) = nu C B (Y ∩ obs d) := by
  rw [nu_eq_sum_pos]
  unfold mass
  conv_lhs => rw [← Finset.filter_univ_mem (worldEv B Y ∩ occ d B)]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [Finset.mem_inter, worldEv, Finset.mem_filter, Finset.mem_univ, true_and, mem_occ]
  rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hzero
  · have hiff : 0 < count d B ℓ ↔ world B ℓ ∈ obs d :=
      ⟨h.2 ℓ hpos, h.1.covers obs actEv ℓ hpos⟩
    by_cases hY : world B ℓ ∈ Y <;> by_cases hO : world B ℓ ∈ obs d <;> simp [hY, hO, hpos, hiff]
  · rw [← hzero]; simp

/-- **SSC screening under `H*`**: with `occ(d)` in place of the `O_d`-runs,
`μ(X ∩ a ∩ occ) · μ(occ) = μ(X ∩ occ) · μ(a ∩ occ)` for pre-query `X`.
Source: `sl-defensible-claims.md` S4 ("the SSC version needs `H*`"); mandate T6
Kind: C
Fidelity: exact
Hyps: none -/
theorem screening_ssc_of_hStar {C : Proc ι acts K} {B : Tree Ω ι acts K} {d : ι}
    (h : HStar obs actEv C B d) {X : Finset Ω} (hX : PreQuery obs C B d X) (a : acts d) :
    mass C B (worldEv B (X ∩ actEv d a) ∩ occ d B) * mass C B (occ d B) =
      mass C B (worldEv B X ∩ occ d B) * mass C B (worldEv B (actEv d a) ∩ occ d B) := by
  have hu : mass C B (occ d B) = nu C B (obs d) := by
    have := mass_worldEv_inter_occ_of_hStar obs actEv h Finset.univ
    rw [Finset.univ_inter] at this
    rw [← this]
    congr 1
    ext ℓ; simp [worldEv]
  rw [mass_worldEv_inter_occ_of_hStar obs actEv h, mass_worldEv_inter_occ_of_hStar obs actEv h,
    mass_worldEv_inter_occ_of_hStar obs actEv h, hu]
  exact screening_recorded obs actEv h.1 hX a

/-! ### Lemma 3 as printed: the per-node reading is empty; the run-level statement

The printed Lemma 3 ([[decision-problems-v2]] §7.3) has two clauses. The first, "conditional on
the realized node, the draw is independent of pre-query events", is **empty** if read per node:
a pre-query event is decided at the node, so the identity
`(∑_{X ∩ edge a} w) · (∑_{below q} w) = (∑_{X ∩ below q} w) · (∑_{edge a} w)` holds for every
leaf weighting `w` whatsoever (`decidedAt_edge_identity`, kind T — it does not test Definition
6; round 1 shipped it as `screening_at_node`, kind P, and the adversarial audit's B1 caught it).
The per-node content of "Definition 6 samples the draw independently of the path" is
`mass_edge` (`NodeSums.lean`): the mass of the `a`-edge below `q` is `C(d_q)(a)` times the mass
below `q`, i.e. the conditional law of the draw given the node is `C(d_q)`. The clause has
content only when the node is *not* conditioned on: aggregated over all `d`-nodes, the draw at
`d` is independent of every event decided at each `d`-node, because that conditional law is the
same `C(d)` at every node (`screening_draw`). The run-level theorem needs only the printed
lemma's "each run realizes at most one `d`-node"; it needs no recording and no hypothesis on
post-query chance. The world-level second clause (`m ⊥ (ℓ, k)` under `ν`) is what needs
recording: see `Overwrite.lean`.
-/

/-- Restricting a sum over the leaves through `q` to an event `X` decided at `q` multiplies it
by the constant `belowInd q X` — for **any** leaf weighting `w`.
Source: none: infrastructure
Kind: L -/
theorem sum_decided_eq_belowInd_mul (B : Tree Ω ι acts K) (q : B.DecNode) (X : Finset Ω)
    (hX : DecidedAt B q X) (w : B.Leaves → K) (P : B.Leaves → Prop) [DecidablePred P]
    (hP : ∀ ℓ, P ℓ → (edgeOf B q ℓ).isSome) :
    (∑ ℓ, if world B ℓ ∈ X ∧ P ℓ then w ℓ else 0) =
      belowInd B q X * ∑ ℓ, if P ℓ then w ℓ else 0 := by
  rcases hX with hin | hout
  · unfold belowInd; rw [if_pos hin, one_mul]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    by_cases hp : P ℓ
    · rw [if_pos hp, if_pos ⟨hin ℓ ((mem_leavesBelow B q ℓ).mpr (hP ℓ hp)), hp⟩]
    · rw [if_neg hp, if_neg (fun h => hp h.2)]
  · unfold belowInd
    by_cases hall : ∀ ℓ ∈ leavesBelow B q, world B ℓ ∈ X
    · -- then nothing lies below `q`; both sides vanish
      rw [if_pos hall, one_mul]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      by_cases hp : P ℓ
      · exact absurd (hall ℓ ((mem_leavesBelow B q ℓ).mpr (hP ℓ hp)))
          (hout ℓ ((mem_leavesBelow B q ℓ).mpr (hP ℓ hp)))
      · rw [if_neg hp, if_neg (fun h => hp h.2)]
    · rw [if_neg hall, zero_mul]
      apply Finset.sum_eq_zero
      intro ℓ _
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hout ℓ ((mem_leavesBelow B q ℓ).mpr (hP ℓ h2)) h1

/-- **The per-node reading of Lemma 3's first clause is empty.** For `X` decided at `q`,
`(∑_{X ∩ edge a} w) · (∑_{below q} w) = (∑_{X ∩ below q} w) · (∑_{edge a} w)` for **every**
leaf weighting `w` — including weightings that bias the draw at `q` by the path. Round 1
shipped the `w = μ_{B,C}` instance as `screening_at_node` (kind P); the adversarial audit (B1)
showed it does not test Definition 6. Kept under an honest name and grade so the point is on
record; it is not a headline. The node-level content of Definition 6 is `mass_edge`; the
run-level content of the clause is `screening_draw`.
Source: [[decision-problems-v2]] §7.3 Lemma 3, first clause, read per node
Kind: T
Fidelity: n/a (true of any weighting) -/
theorem decidedAt_edge_identity (B : Tree Ω ι acts K) (q : B.DecNode) (X : Finset Ω)
    (hX : DecidedAt B q X) (a : acts (pt B q)) (w : B.Leaves → K) :
    (∑ ℓ, if world B ℓ ∈ X ∧ edgeOf B q ℓ = some a then w ℓ else 0) *
        (∑ ℓ, if (edgeOf B q ℓ).isSome then w ℓ else 0) =
      (∑ ℓ, if world B ℓ ∈ X ∧ (edgeOf B q ℓ).isSome then w ℓ else 0) *
        (∑ ℓ, if edgeOf B q ℓ = some a then w ℓ else 0) := by
  rw [sum_decided_eq_belowInd_mul B q X hX w _ (fun ℓ h => by rw [h]; rfl),
    sum_decided_eq_belowInd_mul B q X hX w _ (fun ℓ h => h)]
  ring

/-- **Grouping a run event by the unique `d`-node**: when every positive run meets `d` at most
once, the mass of `{ℓ : P ℓ}` is the sum over the `d`-nodes `q` of the positive mass of the
leaves through `q` satisfying `Q q`, provided `P` agrees with `Q q₀` at the unique `d`-node
`q₀` of each positive path and fails on paths meeting no `d`-node.
Source: none: infrastructure (the grouping step of Lemma 3′'s proof, without recording)
Kind: L -/
theorem mass_eq_sum_fiber_of_count_le_one {C : Proc ι acts K} {B : Tree Ω ι acts K} {d : ι}
    (hcount : ∀ ℓ, 0 < leafLaw C B ℓ → count d B ℓ ≤ 1)
    (P : B.Leaves → Prop) [DecidablePred P] (Q : B.DecNode → B.Leaves → Prop)
    [∀ q, DecidablePred (Q q)] (hQ : ∀ q ℓ, Q q ℓ → (edgeOf B q ℓ).isSome)
    (hPQ : ∀ ℓ q₀, dNodesOn B d ℓ = {q₀} → (P ℓ ↔ Q q₀ ℓ))
    (hP0 : ∀ ℓ, dNodesOn B d ℓ = ∅ → ¬ P ℓ) :
    mass C B (Finset.univ.filter P) =
      ∑ q ∈ fiber B d, ∑ ℓ, if 0 < leafLaw C B ℓ ∧ Q q ℓ then leafLaw C B ℓ else 0 := by
  rw [mass_filter, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hzero
  · have hle := hcount ℓ hpos
    rw [count_eq_card_dNodesOn] at hle
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
    · rw [Finset.card_eq_zero] at h0
      rw [if_neg (hP0 ℓ h0)]
      symm
      apply Finset.sum_eq_zero
      intro q hq
      rw [if_neg]
      rintro ⟨-, hQq⟩
      have hmem : q ∈ dNodesOn B d ℓ := by
        rw [mem_dNodesOn]; exact ⟨(Finset.mem_filter.mp hq).2, hQ q ℓ hQq⟩
      rw [h0] at hmem
      exact Finset.notMem_empty q hmem
    · obtain ⟨q₀, hq₀⟩ := Finset.card_eq_one.mp h1
      rw [sum_fiber_eq_of_singleton hq₀ _ (fun q hq => by
        rw [if_neg]; rintro ⟨-, h⟩; exact hq (hQ q ℓ h))]
      by_cases hPl : P ℓ
      · have hQl : Q q₀ ℓ := (hPQ ℓ q₀ hq₀).mp hPl
        rw [if_pos hPl, if_pos ⟨hpos, hQl⟩]
      · have hQl : ¬ Q q₀ ℓ := fun h => hPl ((hPQ ℓ q₀ hq₀).mpr h)
        rw [if_neg hPl, if_neg (fun h => hQl h.2)]
  · rw [← hzero]; simp

/-- **Run-level screening (Lemma 3's first clause, aggregated over the `d`-nodes)**: if every
positive run meets `d` at most once and every `d`-node met on a positive run decides `X`, then
`μ(X ∩ drew_a) · μ(occ d) = μ(X ∩ occ d) · μ(drew_a)` for every action `a` and every
procedure: on the runs that consult `d`, the draw at `d` is independent of every pre-query
event. No recording (Definition 7) and no hypothesis on post-query chance is needed. What does
the work is that the conditional law of the draw given the node is the same `C(d)` at every
`d`-node (`mass_edge`, Definition 6), so the common factor `C(d)(a)` pulls out of the sum over
nodes; conditioned on a single node the statement is empty (`decidedAt_edge_identity`). The
world-level clause (`m ⊥ (ℓ, k)` under `ν`) needs recording and fails without it
(`Overwrite.lean`).
Source: [[decision-problems-v2]] §7.3 Lemma 3 ("in any instantiation where each run realizes
at most one `d`-node …: conditional on the realized node, the draw is independent of pre-query
events"), nearest true statement of the first clause; mandate T6 ("Lemma 3 as printed")
Kind: P
Fidelity: variant: run-level (the draw `drew d a`, an event of `Leaves(B)`), not world-level
(the action event `a ∈ 𝓔`); "conditional on the realized node" read as "on `occ(d)`", the only
reading with content; the post-query-chance hypothesis is dropped (not needed); the hypotheses
are `PreQuery (fun _ => ⊤)`'s clauses, i.e. `O_d = ⊤`
Hyps: none (`#_d ≤ 1` a.s. and the decidedness of `X` at every `d`-node met on a positive run
are the printed lemma's own hypotheses, stated as tree predicates; both quantify over
**positive** runs only — a zero-mass run may pass a `d`-node that does not decide `X` — which
is Definition 7's a.s. reading, and `PreQuery (fun _ => ⊤)`'s) -/
theorem screening_draw {C : Proc ι acts K} {B : Tree Ω ι acts K} {d : ι}
    (hcount : ∀ ℓ, 0 < leafLaw C B ℓ → count d B ℓ ≤ 1) {X : Finset Ω}
    (hX : ∀ ℓ, 0 < leafLaw C B ℓ → ∀ q, pt B q = d → (edgeOf B q ℓ).isSome → DecidedAt B q X)
    (a : acts d) :
    mass C B (worldEv B X ∩ drew d a B) * mass C B (occ d B) =
      mass C B (worldEv B X ∩ occ d B) * mass C B (drew d a B) := by
  -- the node-level facts, with `O_d = ⊤`
  have hsv : ∀ q ∈ fiber B d, ActiveNode (fun _ => Finset.univ) C B d q →
      SubtreeVeridical (fun _ => Finset.univ) B q :=
    fun _ _ _ _ _ => Finset.mem_univ _
  have hdec : ∀ q ∈ fiber B d, ActiveNode (fun _ => Finset.univ) C B d q → DecidedAt B q X := by
    rintro q hq ⟨ℓ, hpos, -, he⟩
    exact hX ℓ hpos q (Finset.mem_filter.mp hq).2 he
  -- membership in `drew` and `occ` through the unique `d`-node
  have hdrew : ∀ ℓ q₀, dNodesOn B d ℓ = {q₀} →
      (ℓ ∈ drew d a B ↔ edgeS B q₀ ℓ = some ⟨d, a⟩) := by
    intro ℓ q₀ hq₀
    simp only [drew, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mem_draws_iff_exists_edgeS]
    constructor
    · rintro ⟨q, hq⟩
      have hmem : q ∈ dNodesOn B d ℓ := by
        rw [mem_dNodesOn]; exact ⟨pt_eq_of_edgeS B q ℓ hq, isSome_of_edgeS B q ℓ hq⟩
      rw [hq₀, Finset.mem_singleton] at hmem
      rw [← hmem]; exact hq
    · intro h; exact ⟨q₀, h⟩
  have hdrew0 : ∀ ℓ, dNodesOn B d ℓ = ∅ → ℓ ∉ drew d a B := by
    intro ℓ h0 hmem
    simp only [drew, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rw [mem_draws_iff_exists_edgeS] at hmem
    obtain ⟨q, hq⟩ := hmem
    have hm : q ∈ dNodesOn B d ℓ := by
      rw [mem_dNodesOn]; exact ⟨pt_eq_of_edgeS B q ℓ hq, isSome_of_edgeS B q ℓ hq⟩
    rw [h0] at hm
    exact Finset.notMem_empty q hm
  have hocc : ∀ ℓ q₀, dNodesOn B d ℓ = {q₀} → (0 < count d B ℓ ↔ (edgeOf B q₀ ℓ).isSome) := by
    intro ℓ q₀ hq₀
    have hm : q₀ ∈ dNodesOn B d ℓ := by rw [hq₀]; exact Finset.mem_singleton_self _
    rw [mem_dNodesOn] at hm
    rw [count_eq_card_dNodesOn, hq₀, Finset.card_singleton]
    exact ⟨fun _ => hm.2, fun _ => Nat.one_pos⟩
  have hocc0 : ∀ ℓ, dNodesOn B d ℓ = ∅ → ¬ 0 < count d B ℓ := by
    intro ℓ h0
    rw [count_eq_card_dNodesOn, h0, Finset.card_empty]
    exact lt_irrefl 0
  -- the four masses as node sums
  have h1 : mass C B (worldEv B X ∩ drew d a B) =
      ∑ q ∈ fiber B d, belowInd B q X * ((C d).w a * obsMassBelow (fun _ => Finset.univ) C B d q) := by
    have e : worldEv B X ∩ drew d a B =
        Finset.univ.filter fun ℓ => world B ℓ ∈ X ∧ ℓ ∈ drew d a B := by
      ext ℓ; simp [worldEv]
    rw [e, mass_eq_sum_fiber_of_count_le_one hcount _
      (fun q ℓ => world B ℓ ∈ X ∧ edgeS B q ℓ = some ⟨d, a⟩)
      (fun q ℓ h => isSome_of_edgeS B q ℓ h.2)
      (fun ℓ q₀ hq₀ => and_congr_right fun _ => hdrew ℓ q₀ hq₀)
      (fun ℓ h0 h => hdrew0 ℓ h0 h.2)]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [← node_mass_edge (fun _ => Finset.univ) C B d q (Finset.mem_filter.mp hq).2 (hsv q hq) a,
      ← node_sum_inter_X (fun _ => Finset.univ) C B d q X (hdec q hq)
        (fun ℓ => edgeS B q ℓ = some ⟨d, a⟩) (fun ℓ h => isSome_of_edgeS B q ℓ h)]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp only [Finset.mem_univ, true_and]
  have h2 : mass C B (occ d B) = ∑ q ∈ fiber B d, obsMassBelow (fun _ => Finset.univ) C B d q := by
    unfold occ
    rw [mass_eq_sum_fiber_of_count_le_one hcount _ (fun q ℓ => (edgeOf B q ℓ).isSome)
      (fun _ _ h => h) hocc hocc0]
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold obsMassBelow
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp only [Finset.mem_univ, true_and]
  have h3 : mass C B (worldEv B X ∩ occ d B) =
      ∑ q ∈ fiber B d, belowInd B q X * obsMassBelow (fun _ => Finset.univ) C B d q := by
    have e : worldEv B X ∩ occ d B =
        Finset.univ.filter fun ℓ => world B ℓ ∈ X ∧ 0 < count d B ℓ := by
      ext ℓ; simp [worldEv, occ]
    rw [e, mass_eq_sum_fiber_of_count_le_one hcount _
      (fun q ℓ => world B ℓ ∈ X ∧ (edgeOf B q ℓ).isSome)
      (fun _ _ h => h.2)
      (fun ℓ q₀ hq₀ => and_congr_right fun _ => hocc ℓ q₀ hq₀)
      (fun ℓ h0 h => hocc0 ℓ h0 h.2)]
    refine Finset.sum_congr rfl fun q hq => ?_
    unfold obsMassBelow
    rw [← node_sum_inter_X (fun _ => Finset.univ) C B d q X (hdec q hq)
      (fun ℓ => (edgeOf B q ℓ).isSome) (fun _ h => h)]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp only [Finset.mem_univ, true_and]
  have h4 : mass C B (drew d a B) =
      ∑ q ∈ fiber B d, (C d).w a * obsMassBelow (fun _ => Finset.univ) C B d q := by
    conv_lhs => rw [← Finset.filter_univ_mem (drew d a B)]
    rw [mass_eq_sum_fiber_of_count_le_one hcount _ (fun q ℓ => edgeS B q ℓ = some ⟨d, a⟩)
      (fun q ℓ h => isSome_of_edgeS B q ℓ h) hdrew hdrew0]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [← node_mass_edge (fun _ => Finset.univ) C B d q (Finset.mem_filter.mp hq).2 (hsv q hq) a]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp only [Finset.mem_univ, true_and]
  rw [h1, h2, h3, h4]
  simp only [mul_left_comm _ ((C d).w a), ← Finset.mul_sum]
  ring

/-- **Run-level screening, conditional form**: under `μ(drew_a) > 0` and `μ(occ d) > 0`,
`μ(X ∩ drew_a) / μ(drew_a) = μ(X ∩ occ d) / μ(occ d)`.
Source: [[decision-problems-v2]] §7.3 Lemma 3, first clause
Kind: C -/
theorem screening_draw_div {C : Proc ι acts K} {B : Tree Ω ι acts K} {d : ι}
    (hcount : ∀ ℓ, 0 < leafLaw C B ℓ → count d B ℓ ≤ 1) {X : Finset Ω}
    (hX : ∀ ℓ, 0 < leafLaw C B ℓ → ∀ q, pt B q = d → (edgeOf B q ℓ).isSome → DecidedAt B q X)
    (a : acts d) (ha : 0 < mass C B (drew d a B)) (hO : 0 < mass C B (occ d B)) :
    mass C B (worldEv B X ∩ drew d a B) / mass C B (drew d a B) =
      mass C B (worldEv B X ∩ occ d B) / mass C B (occ d B) := by
  rw [div_eq_div_iff ha.ne' hO.ne']
  exact screening_draw hcount hX a

end Tree

end Cleanroom.Found.DpCoreTree
