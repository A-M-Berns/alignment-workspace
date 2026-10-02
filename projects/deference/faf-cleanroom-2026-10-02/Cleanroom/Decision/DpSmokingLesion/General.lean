import Cleanroom.Decision.DpSmokingLesion.Defs
import Cleanroom.Found.DpCoreTree.Faithful

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The general theorems: recording, the referents, post-query screening

The finite-tree theorems of [[dp-smoking-lesion-mandate]] T1(c) and T3(a)–(b), stated over
`dp-core-tree`'s objects for an arbitrary finite tree, point, observation and action events.

* **T3(a), EV = R1-state under `RecordsFor` for `C` alone** (`paySum_actEv_inter_obs_eq_deviatePure`,
  `nu_actEv_inter_obs_eq_deviatePure`, `prop13_ev_eq_r1State`): on a recorded point,
  `∑_{λ ⊨ a ∧ O_d} μ_C r = C(d)(a) · ∑_{λ ⊨ O_d} μ_{C[d↦a]} r` and
  `ν_C(a ∧ O_d) = C(d)(a) · ν_{C[d↦a]}(O_d)`, so the evidential statistic
  `paySum(a ∧ O_d)/ν(a ∧ O_d)` and the all-instance deviation statistic
  `paySum_{C[d↦a]}(O_d)/ν_{C[d↦a]}(O_d)` coincide (cross-multiplied). Recording is assumed
  **for `C` only** (dp-sl-2-061 (i) confirmed): the deviated law's positive `O_d`-runs are
  exactly `C`'s positive `O_d`-runs that drew `a`, because a leaf of zero `C`-mass has zero
  `C[d↦a]`-mass unless `C(d)(a) = 0` (`leafLaw_eq_zero_imp_deviatePure`), and on positive
  `O_d`-runs the act event is the draw (clauses 3–4).
* **T3(b), EV = R2-SIA = R2-real under `H*`** (`paySum_actEv_inter_obs_eq_mul_r2Sia`,
  `nu_obs_eq_fiberMass`, `r2Real_eq_r2Sia_of_hStar`, `r2RealAll_eq_r2Sia_of_hStar`): under `H*`,
  `∑_{λ ⊨ a ∧ O_d} μ_C r = C(d)(a) · ∑_q forcedBelow_q(a)` and `ν(O_d) = ∑_q R_q`, and both
  readings of R2-real's averaging set give the same sums as the full fiber (the nodes they omit
  have reach `0`). Per node the content is `edge_paySum_eq_mul_forcedBelow`: the payoff mass of
  the `a`-edge of `q` is `C(d_q)(a)` times the single-instance forcing mass, from
  `dp-core-tree`'s `leafLawNode_update_of_edge`.
* **T1(c), post-query screening** (`postQuery_screening_recorded`): under recording at an
  `O_d = ⊤` point and post-query independence of `X` from the draw
  (`PostQueryIndep`), `ν(X ∧ a) · ν(b) = ν(X ∧ b) · ν(a)` for all actions `a, b` — the
  `k`-clause of the repaired Lemma 3, with `X = evK` (`nuFlat_of_recordsFor_postQueryIndep`).
-/

namespace Cleanroom.Decision.DpSmokingLesion

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] {acts : ι → Type}
  [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]

/-! ## Zero mass propagates to the deviation -/

/-- If the draw product under `C` vanishes on a list, then `C(d)(a)` times the draw product
under `C[d↦a]` vanishes too (a vanishing draw at `d` is either `a` itself, killing `C(d)(a)`,
or another action, killed by the deviation).
Source: none: infrastructure
Kind: L -/
theorem prod_draws_deviatePure_of_eq_zero (C : Proc ι acts K) (d : ι) (a : acts d) :
    (L : List (Σ d : ι, acts d)) → (L.map fun x => (C x.1).w x.2).prod = 0 →
      (C d).w a * (L.map fun x => ((C.deviatePure d a) x.1).w x.2).prod = 0
  | [], h => by simp at h
  | x :: L, h => by
      simp only [List.map_cons, List.prod_cons] at h ⊢
      rcases mul_eq_zero.mp h with hx | hL
      · obtain ⟨d', b⟩ := x
        simp only at hx ⊢
        by_cases hd : d' = d
        · subst hd
          by_cases hb : b = a
          · subst hb; rw [hx]; ring
          · simp [Proc.deviatePure, Proc.deviate_same, FinDistr.pure_w, hb]
        · rw [Proc.deviatePure, Proc.deviate_ne C _ hd, hx]; ring
      · have ih := prod_draws_deviatePure_of_eq_zero C d a L hL
        calc (C d).w a * (((C.deviatePure d a) x.1).w x.2 *
              (L.map fun x => ((C.deviatePure d a) x.1).w x.2).prod)
            = ((C.deviatePure d a) x.1).w x.2 *
              ((C d).w a * (L.map fun x => ((C.deviatePure d a) x.1).w x.2).prod) := by ring
          _ = 0 := by rw [ih, mul_zero]

/-- A leaf of zero `C`-mass has zero `C[d↦a]`-mass unless `C(d)(a) = 0`:
`μ_C(ℓ) = 0 → C(d)(a) · μ_{C[d↦a]}(ℓ) = 0`.
Source: none: infrastructure (the lemma behind "recording for `C` alone suffices",
dp-sl-2-061 (i))
Kind: L -/
theorem leafLaw_eq_zero_imp_deviatePure (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)
    (a : acts d) (ℓ : B.Leaves) (h : leafLaw C B ℓ = 0) :
    (C d).w a * leafLaw (C.deviatePure d a) B ℓ = 0 := by
  rw [leafLaw_eq_chanceWeight_mul_drawsWeight] at h ⊢
  unfold drawsWeight at h ⊢
  rcases mul_eq_zero.mp h with hc | hp
  · rw [hc]; ring
  · have := prod_draws_deviatePure_of_eq_zero C d a _ hp
    calc (C d).w a * (chanceWeight B ℓ *
          ((draws B ℓ).map fun x => ((C.deviatePure d a) x.1).w x.2).prod)
        = chanceWeight B ℓ * ((C d).w a *
          ((draws B ℓ).map fun x => ((C.deviatePure d a) x.1).w x.2).prod) := by ring
      _ = 0 := by rw [this, mul_zero]

/-! ## T3(a): the evidential statistic is the all-instance deviation statistic -/

section r1

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
variable (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)

/-- **The pointwise identity**: on a recorded point, for every leaf,
`[λ(ℓ) ⊨ a ∧ O_d] · μ_C(ℓ) = C(d)(a) · [λ(ℓ) ⊨ O_d] · μ_{C[d↦a]}(ℓ)`. On a positive `O_d`-leaf
the act event is the draw at the unique `d`-node (clauses 3–4), and the draw factors out of
the law (`leafLaw_eq_mul_deviatePure_of_drew`) or kills the deviated law
(`leafLaw_deviatePure_eq_zero_of_other`); a zero-mass leaf is handled by
`leafLaw_eq_zero_imp_deviatePure`.
Source: `sl-workflow` FA-4 / FA-20′ ("conditioning on the recorded draw is the deviation");
[[decision-problems-v2]] Definition 7 clauses 3–4
Kind: P -/
theorem ind_actEv_obs_eq_deviatePure (hrec : RecordsFor obs actEv C B d) (a : acts d)
    (ℓ : B.Leaves) :
    (if world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d then leafLaw C B ℓ else 0) =
      (C d).w a * (if world B ℓ ∈ obs d then leafLaw (C.deviatePure d a) B ℓ else 0) := by
  by_cases hobs : world B ℓ ∈ obs d
  · simp only [hobs, and_true, if_true]
    rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hzero
    · obtain ⟨q₀, hq₀⟩ := dNodesOn_eq_singleton_of_recorded obs actEv hrec hpos hobs
      have hcount : count d B ℓ = 1 := (hrec ℓ hpos hobs).1
      have hiff := actEv_iff_edgeS_of_recorded obs actEv hrec hpos hobs hq₀ a
      by_cases hact : world B ℓ ∈ actEv d a
      · rw [if_pos hact]
        have hmem : (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ :=
          (mem_draws_iff_exists_edgeS B ℓ _).mpr ⟨q₀, hiff.mp hact⟩
        exact leafLaw_eq_mul_deviatePure_of_drew C B d a ℓ hmem hcount.le
      · rw [if_neg hact]
        have hq₀mem : q₀ ∈ dNodesOn B d ℓ := by rw [hq₀]; exact Finset.mem_singleton_self _
        rw [mem_dNodesOn] at hq₀mem
        obtain ⟨hpt, he⟩ := hq₀mem
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp he
        have hbS : edgeS B q₀ ℓ = some ⟨pt B q₀, b⟩ := (edgeS_eq_some_iff B q₀ ℓ b).mpr hb
        have hmemb : (⟨pt B q₀, b⟩ : Σ d, acts d) ∈ draws B ℓ :=
          (mem_draws_iff_exists_edgeS B ℓ _).mpr ⟨q₀, hbS⟩
        subst hpt
        have hba : b ≠ a := by
          intro hba
          subst hba
          exact hact (hiff.mpr hbS)
        rw [leafLaw_deviatePure_eq_zero_of_other C B _ a b hba ℓ hmemb, mul_zero]
    · have h0 := leafLaw_eq_zero_imp_deviatePure C B d a ℓ hzero.symm
      rw [h0]
      split_ifs <;> simp [← hzero]
  · simp only [hobs, and_false, if_false, mul_zero]

/-- **T3(a), payoff mass**: under `RecordsFor` for `C`,
`∑_{λ ⊨ a ∧ O_d} μ_C(ℓ) r(ℓ) = C(d)(a) · ∑_{λ ⊨ O_d} μ_{C[d↦a]}(ℓ) r(ℓ)`.
Source: `sl-defensible-claims.md` S1 (Proposition 13, "`V_{s_d}(a) = 𝔼_{μ_{C[d↦a]}}[r ∣ O_d]`");
dp-sl-2-061 (i) ("recording for the given `C` suffices")
Kind: P
Fidelity: exact (multiplicative; no positivity needed)
Hyps: (a) `RecordsFor obs actEv C B d` — Definition 7 for `C` alone -/
theorem paySum_actEv_inter_obs_eq_deviatePure (hrec : RecordsFor obs actEv C B d) (a : acts d) :
    paySum C B (actEv d a ∩ obs d) = (C d).w a * paySum (C.deviatePure d a) B (obs d) := by
  rw [paySum_eq_sum_ite, paySum_eq_sum_ite, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have h := ind_actEv_obs_eq_deviatePure obs actEv C B d hrec a ℓ
  simp only [Finset.mem_inter]
  have e1 : (if world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d then leafLaw C B ℓ * payoff B ℓ
      else 0) = (if world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d then leafLaw C B ℓ else 0) *
        payoff B ℓ := by split_ifs <;> simp
  have e2 : (if world B ℓ ∈ obs d then leafLaw (C.deviatePure d a) B ℓ * payoff B ℓ else 0) =
      (if world B ℓ ∈ obs d then leafLaw (C.deviatePure d a) B ℓ else 0) * payoff B ℓ := by
    split_ifs <;> simp
  rw [e1, e2, h]; ring

/-- **T3(a), normaliser**: under `RecordsFor` for `C`, `ν_C(a ∧ O_d) = C(d)(a) · ν_{C[d↦a]}(O_d)`.
(With `nu_actEv_inter_obs_of_recordsFor` this also says `ν_{C[d↦a]}(O_d) = ν_C(O_d)` when
`C(d)(a) > 0`.)
Source: `sl-defensible-claims.md` S1 (Proposition 13); dp-sl-2-061 (i)
Kind: P
Fidelity: exact
Hyps: (a) `RecordsFor obs actEv C B d` for `C` alone -/
theorem nu_actEv_inter_obs_eq_deviatePure (hrec : RecordsFor obs actEv C B d) (a : acts d) :
    nu C B (actEv d a ∩ obs d) = (C d).w a * nu (C.deviatePure d a) B (obs d) := by
  rw [nu_eq_sum, nu_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have h := ind_actEv_obs_eq_deviatePure obs actEv C B d hrec a ℓ
  simpa only [Finset.mem_inter] using h

/-- **Proposition 13(a): EV = R1-state under `RecordsFor` for `C` alone**, cross-multiplied:
`paySum_C(a ∧ O_d) · ν_{C[d↦a]}(O_d) = paySum_{C[d↦a]}(O_d) · ν_C(a ∧ O_d)` for every action
`a` (with `0 < ν_C(a ∧ O_d)` this is `𝔼_{μ_C}[r ∣ a ∧ O_d] = 𝔼_{μ_{C[d↦a]}}[r ∣ O_d]`). The
evidential value enters only through clause 2 of Definition 8 (a hypothesis instance at the
state, never a theorem here); this is the identity between the *statistics*.
Source: `sl-defensible-claims.md` S1 line 20 (Proposition 13, the R1-state clause); dp-sl-011;
dp-sl-2-061 (i)
Kind: P
Fidelity: exact (cross-multiplied; recording for `C` only — the source's "for `C` suffices at
strict/limit" confirmed)
Hyps: (a) `RecordsFor obs actEv C B d` (Definition 7 for `C`) -/
theorem prop13_ev_eq_r1State (hrec : RecordsFor obs actEv C B d) (a : acts d) :
    paySum C B (actEv d a ∩ obs d) * r1StateNu obs C B d a =
      r1StatePay obs C B d a * nu C B (actEv d a ∩ obs d) := by
  unfold r1StateNu r1StatePay
  rw [paySum_actEv_inter_obs_eq_deviatePure obs actEv C B d hrec a,
    nu_actEv_inter_obs_eq_deviatePure obs actEv C B d hrec a]
  ring

end r1

/-! ## Forcing at a node: the edge payoff mass is `C(d_q)(a)` times `forcedBelow` -/

section forcing

variable (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- A node of zero reach has no leaf of positive mass below it, under any node policy.
Source: none: infrastructure
Kind: L -/
theorem leafLawNode_eq_zero_of_reachNode_eq_zero :
    (B : Tree Ω ι acts K) → ∀ (p : NodePolicy B) (q : B.DecNode) (ℓ : B.Leaves),
      reachNode B p q = 0 → (edgeOf B q ℓ).isSome → leafLawNode B p ℓ = 0
  | leaf _ _, _, q, _, _, _ => q.elim
  | chance _ β child, p, ⟨i, q⟩, ⟨j, ℓ⟩, hr, he => by
      by_cases hji : j = i
      · subst hji
        simp only [edgeOf_chance, dite_true] at he
        simp only [reachNode_chance] at hr
        simp only [leafLawNode_chance]
        rcases mul_eq_zero.mp hr with h0 | h0
        · rw [h0, zero_mul]
        · rw [leafLawNode_eq_zero_of_reachNode_eq_zero (child j) _ q ℓ h0 he, mul_zero]
      · simp [edgeOf_chance, hji] at he
  | decision _ _, _, none, ⟨_, _⟩, hr, _ => by simp at hr
  | decision _ child, p, some ⟨c, q⟩, ⟨b, ℓ⟩, hr, he => by
      by_cases hbc : b = c
      · subst hbc
        simp only [edgeOf_decision_some, dite_true] at he
        simp only [reachNode_decision_some] at hr
        simp only [leafLawNode_decision]
        rcases mul_eq_zero.mp hr with h0 | h0
        · rw [h0, zero_mul]
        · rw [leafLawNode_eq_zero_of_reachNode_eq_zero (child b) _ q ℓ h0 he, mul_zero]
      · simp [edgeOf_decision_some, hbc] at he

/-- `R_q = 0` iff every leaf below `q` has zero mass.
Source: none: infrastructure
Kind: L -/
theorem reach_eq_zero_iff (q : B.DecNode) :
    reach C B q = 0 ↔ ∀ ℓ, (edgeOf B q ℓ).isSome → leafLaw C B ℓ = 0 := by
  rw [reach_eq_mass_leavesBelow]
  unfold mass
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun ℓ _ => leafLaw_nonneg C B ℓ)]
  simp only [mem_leavesBelow]

/-- The forcing mass at a node of zero reach is zero.
Source: none: infrastructure
Kind: L -/
theorem forcedBelow_eq_zero_of_reach_eq_zero (q : B.DecNode) (a : acts (pt B q))
    (h : reach C B q = 0) : forcedBelow B (NodePolicy.ofProc C B) q a = 0 := by
  unfold forcedBelow
  apply Finset.sum_eq_zero
  intro ℓ hℓ
  rw [mem_leavesBelow] at hℓ
  have hr : reachNode B ((NodePolicy.ofProc C B).update q (FinDistr.pure a)) q = 0 := by
    rw [reachNode_update_self, reachNode_ofProc]; exact h
  rw [leafLawNode_eq_zero_of_reachNode_eq_zero B _ q ℓ hr hℓ, zero_mul]

/-- **The edge payoff mass is the forcing mass scaled by the draw weight**: at any node `q`,
`∑_{ℓ : edge_q(ℓ) = a} μ_C(ℓ) r(ℓ) = C(d_q)(a) · forcedBelow_q(a)` — Definition 6's independent
draw factors out of every leaf below the `a`-edge (`leafLawNode_update_of_edge`), and the
forced law vanishes on the other edges.
Source: [[decision-problems-v2]] §8 (`R_q · G_q(a)`, "forcing the single instance"); mandate
T3(b) ("per node `forcedBelow` at `pure a` is the `a`-edge's payoff mass divided by `C(d)(a)`")
Kind: P -/
theorem edge_paySum_eq_mul_forcedBelow (q : B.DecNode) (a : acts (pt B q)) :
    (∑ ℓ, if edgeOf B q ℓ = some a then leafLaw C B ℓ * payoff B ℓ else 0) =
      (C (pt B q)).w a * forcedBelow B (NodePolicy.ofProc C B) q a := by
  unfold forcedBelow leavesBelow
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases he : edgeOf B q ℓ = some a
  · rw [if_pos he, if_pos (by rw [he]; rfl)]
    have h1 := leafLawNode_update_of_edge B (NodePolicy.ofProc C B) q ℓ
      (NodePolicy.ofProc C B q) a he
    rw [NodePolicy.update_eq_self] at h1
    rw [← leafLawNode_ofProc C B ℓ, h1]
    simp only [NodePolicy.ofProc]; ring
  · rw [if_neg he]
    by_cases hs : (edgeOf B q ℓ).isSome
    · rw [if_pos hs]
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hs
      have hba : b ≠ a := fun h => he (by rw [hb, h])
      rw [leafLawNode_update_of_edge B (NodePolicy.ofProc C B) q ℓ (FinDistr.pure a) b hb]
      simp [FinDistr.pure_w, hba]
    · rw [if_neg hs]; ring

/-- The mass of the leaves below `q` is `R_q`, as an indicator sum.
Source: none: infrastructure
Kind: L -/
theorem sum_isSome_eq_reach (q : B.DecNode) :
    (∑ ℓ, if (edgeOf B q ℓ).isSome then leafLaw C B ℓ else 0) = reach C B q := by
  rw [reach_eq_mass_leavesBelow]
  unfold mass leavesBelow
  rw [Finset.sum_filter]

end forcing

/-! ## T3(b): under `H*`, EV = R2-SIA = R2-real -/

section hstar

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
variable (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)

/-- Under `H*`, a `d`-node met by no positive `O_d`-run is met by no positive run at all, so
its reach is `0`.
Source: `sl-synthesis.md` line 20 (`H*`'s second clause)
Kind: L -/
theorem reach_eq_zero_of_not_active_of_hStar (hH : HStar obs actEv C B d) (q : B.DecNode)
    (hq : pt B q = d) (hna : ¬ ActiveNode obs C B d q) : reach C B q = 0 := by
  rw [reach_eq_zero_iff]
  intro ℓ he
  by_contra hne
  have hpos : 0 < leafLaw C B ℓ := (leafLaw_nonneg C B ℓ).lt_of_ne (Ne.symm hne)
  have hc : 0 < count d B ℓ := by
    have := count_pos_of_edge B q ℓ he
    rwa [hq] at this
  exact hna ⟨ℓ, hpos, hH.2 ℓ hpos hc, he⟩

/-- Under `H*`, every active `d`-node is subtree-veridical (Definition 7 clause 2) and a.s.
node-action-veridical (clause 3 at every positive leaf below it).
Source: [[decision-problems-v2]] Definition 7 clauses 2–3; `sl-synthesis.md` line 20
Kind: L -/
theorem active_sv_nav_of_hStar (hH : HStar obs actEv C B d) (q : B.DecNode) (hq : pt B q = d)
    (hact : ActiveNode obs C B d q) :
    SubtreeVeridical obs B q ∧ NodeActionVeridicalAS actEv C B q := by
  obtain ⟨ℓ₀, hpos₀, hobs₀, he₀⟩ := hact
  obtain ⟨a₀, ha₀⟩ := Option.isSome_iff_exists.mp he₀
  have hsv := ((hH.1 ℓ₀ hpos₀ hobs₀).2 q hq a₀ ha₀).1
  refine ⟨hsv, fun ℓ a hpos ha => ?_⟩
  have hobs : world B ℓ ∈ obs d := by
    have := hsv ℓ ((mem_leavesBelow B q ℓ).mpr (by rw [ha]; rfl))
    rwa [hq] at this
  exact ((hH.1 ℓ hpos hobs).2 q hq a ha).2.1

/-- The sums over the fiber transported along `pt q = d`, as a function of the node.
Source: none: infrastructure
Kind: D -/
def fiberTerm (a : acts d) (q : B.DecNode) : K :=
  if h : pt B q = d then forcedBelow B (NodePolicy.ofProc C B) q (transport h.symm a) else 0

/-- Under `H*`, `∑_{λ ⊨ a ∧ O_d} μ_C r = ∑_{q ∈ svFiber} ∑_{edge_q = a} μ_C r`: grouping the
positive `O_d`-runs by their unique subtree-veridical `d`-node.
Source: none: infrastructure
Kind: L -/
theorem paySum_actEv_inter_obs_eq_sum_svFiber (hrec : RecordsFor obs actEv C B d) (a : acts d) :
    paySum C B (actEv d a ∩ obs d) =
      ∑ q ∈ svFiber obs B d, ∑ ℓ, if edgeS B q ℓ = some ⟨d, a⟩ then leafLaw C B ℓ * payoff B ℓ
        else 0 := by
  rw [paySum_eq_sum_ite, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have h := ind_actEv_eq_sum_svFiber obs actEv C B hrec a Finset.univ ℓ
  simp only [Finset.mem_univ, true_and, and_true] at h
  have e1 : (if world B ℓ ∈ actEv d a ∩ obs d then leafLaw C B ℓ * payoff B ℓ else 0) =
      (if world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d then leafLaw C B ℓ else 0) * payoff B ℓ := by
    simp only [Finset.mem_inter]; split_ifs <;> simp
  rw [e1, h, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs <;> simp

/-- `svFiber ⊆ fiber`. Source: none: infrastructure. Kind: L -/
theorem svFiber_subset_fiber : svFiber obs B d ⊆ fiber B d := by
  intro q hq
  rw [mem_svFiber] at hq
  rw [fiber, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hq.1⟩

/-- Under `H*`, a `d`-node that is not subtree-veridical has reach `0`.
Source: none: infrastructure
Kind: L -/
theorem reach_eq_zero_of_not_sv_of_hStar (hH : HStar obs actEv C B d) (q : B.DecNode)
    (hq : pt B q = d) (hnsv : ¬ SubtreeVeridical obs B q) : reach C B q = 0 := by
  apply reach_eq_zero_of_not_active_of_hStar obs actEv C B d hH q hq
  intro hact
  exact hnsv (active_sv_nav_of_hStar obs actEv C B d hH q hq hact).1

/-- **T3(b), payoff mass**: under `H*`,
`∑_{λ ⊨ a ∧ O_d} μ_C(ℓ) r(ℓ) = C(d)(a) · ∑_{q ∈ fiber d} forcedBelow_q(a) = C(d)(a) · R2-SIA(a)`.
Source: `sl-defensible-claims.md` S1 (Proposition 13, "`= ∑_q R_q G_q(C, a) / ∑_q R_q`");
dp-sl-011
Kind: P
Fidelity: exact (multiplicative). The mandate's line `paySum(a ∧ O_d) · fiberMass = r2Sia ·
ν(O_d)` omits the factor `C(d)(a)`; the correct cross-multiplied form is
`prop13_ev_eq_r2Sia` below
Hyps: (a) `HStar obs actEv C B d` -/
theorem paySum_actEv_inter_obs_eq_mul_r2Sia (hH : HStar obs actEv C B d) (a : acts d) :
    paySum C B (actEv d a ∩ obs d) = (C d).w a * r2Sia C B d a := by
  rw [paySum_actEv_inter_obs_eq_sum_svFiber obs actEv C B d hH.1 a]
  unfold r2Sia
  rw [Finset.mul_sum]
  rw [← Finset.sum_subset (svFiber_subset_fiber obs B d) (fun q hq hnsv => by
    have hpt := (Finset.mem_filter.mp hq).2
    have hnsv' : ¬ SubtreeVeridical obs B q :=
      fun h => hnsv ((mem_svFiber obs B d q).mpr ⟨hpt, h⟩)
    have h0 := reach_eq_zero_of_not_sv_of_hStar obs actEv C B d hH q hpt hnsv'
    subst hpt
    simp only [dite_true, transport_rfl]
    rw [forcedBelow_eq_zero_of_reach_eq_zero C B q a h0, mul_zero])]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hpt := ((mem_svFiber obs B d q).mp hq).1
  subst hpt
  simp only [dite_true, transport_rfl, edgeS_eq_some_iff]
  exact edge_paySum_eq_mul_forcedBelow C B q a

/-- **T3(b), normaliser**: under `H*`, `ν_C(O_d) = ∑_{q ∈ fiber d} R_q`.
Source: `sl-defensible-claims.md` S1 (Proposition 13); mandate T3(b) ("`reach` sums to
`ν(O_d)` under `H*`")
Kind: P
Fidelity: exact
Hyps: (a) `HStar obs actEv C B d` -/
theorem nu_obs_eq_fiberMass (hH : HStar obs actEv C B d) : nu C B (obs d) = fiberMass C B d := by
  have h1 : nu C B (obs d) = ∑ q ∈ svFiber obs B d, reach C B q := by
    rw [nu_eq_sum, Finset.sum_congr rfl (fun ℓ _ => ind_obs_eq_sum_svFiber obs actEv C B hH.1 ℓ),
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => sum_isSome_eq_reach C B q
  rw [h1]
  unfold fiberMass
  apply Finset.sum_subset (svFiber_subset_fiber obs B d)
  intro q hq hnsv
  have hpt := (Finset.mem_filter.mp hq).2
  exact reach_eq_zero_of_not_sv_of_hStar obs actEv C B d hH q hpt
    (fun h => hnsv ((mem_svFiber obs B d q).mpr ⟨hpt, h⟩))

/-- **Proposition 13(b): EV = R2-SIA under `H*`**, cross-multiplied:
`paySum_C(a ∧ O_d) · fiberMass = r2Sia(a) · ν_C(a ∧ O_d)` (with `0 < ν(a ∧ O_d)`:
`𝔼[r ∣ a ∧ O_d] = ∑_q R_q G_q(a) / ∑_q R_q`).
Source: `sl-defensible-claims.md` S1 line 20 (Proposition 13, the R2-SIA clause); dp-sl-011
Kind: C
Fidelity: exact (cross-multiplied)
Hyps: (a) `HStar obs actEv C B d` -/
theorem prop13_ev_eq_r2Sia (hH : HStar obs actEv C B d) (a : acts d) :
    paySum C B (actEv d a ∩ obs d) * fiberMass C B d =
      r2Sia C B d a * nu C B (actEv d a ∩ obs d) := by
  rw [paySum_actEv_inter_obs_eq_mul_r2Sia obs actEv C B d hH a,
    nu_actEv_inter_obs_of_recordsFor obs actEv C B hH.1 a, nu_obs_eq_fiberMass obs actEv C B d hH]
  ring

/-- Under `H*`, the reading-2 fiber is the fiber up to nodes of zero reach: an active `d`-node
is in it, and an inactive `d`-node has reach `0`.
Source: dp-sl-2-058 (reading 2 "collapses into `H*`")
Kind: L -/
theorem sum_realFiber_eq_of_hStar (hH : HStar obs actEv C B d) (f : B.DecNode → K)
    (hf : ∀ q, pt B q = d → reach C B q = 0 → f q = 0) :
    ∑ q ∈ realFiber obs actEv C B d, f q = ∑ q ∈ fiber B d, f q := by
  apply Finset.sum_subset
  · intro q hq
    have := ((mem_realFiber obs actEv C B d q).mp hq).1
    rw [fiber, Finset.mem_filter]; exact ⟨Finset.mem_univ _, this⟩
  · intro q hq hnot
    have hpt := (Finset.mem_filter.mp hq).2
    apply hf q hpt
    apply reach_eq_zero_of_not_active_of_hStar obs actEv C B d hH q hpt
    intro hact
    apply hnot
    exact (mem_realFiber obs actEv C B d q).mpr
      ⟨hpt, (active_sv_nav_of_hStar obs actEv C B d hH q hpt hact).2, hact⟩

/-- Under `H*`, the reading-1 fiber is the fiber up to nodes of zero reach.
Source: dp-sl-2-058 (reading 1)
Kind: L -/
theorem sum_realFiberAll_eq_of_hStar (hH : HStar obs actEv C B d) (f : B.DecNode → K)
    (hf : ∀ q, pt B q = d → reach C B q = 0 → f q = 0) :
    ∑ q ∈ realFiberAll actEv C B d, f q = ∑ q ∈ fiber B d, f q := by
  apply Finset.sum_subset
  · intro q hq
    have := ((mem_realFiberAll actEv C B d q).mp hq).1
    rw [fiber, Finset.mem_filter]; exact ⟨Finset.mem_univ _, this⟩
  · intro q hq hnot
    have hpt := (Finset.mem_filter.mp hq).2
    apply hf q hpt
    apply reach_eq_zero_of_not_active_of_hStar obs actEv C B d hH q hpt
    intro hact
    apply hnot
    exact (mem_realFiberAll actEv C B d q).mpr
      ⟨hpt, (active_sv_nav_of_hStar obs actEv C B d hH q hpt hact).2⟩

/-- **Proposition 13(b), R2-real = R2-SIA under `H*`** (reading 2): the averaging set of
R2-real is the fiber up to nodes of reach `0`, so both the numerator and the normaliser agree.
Source: `sl-defensible-claims.md` S1 (Proposition 13, "R2-real … under `H*`"); dp-sl-2-058
reading 2
Kind: P
Fidelity: variant: construal — R2-real read as reading 2 (disclosed in `Defs.lean`)
Hyps: (a) `HStar obs actEv C B d` -/
theorem r2Real_eq_r2Sia_of_hStar (hH : HStar obs actEv C B d) (a : acts d) :
    r2RealPay obs actEv C B d a = r2Sia C B d a ∧ r2RealMass obs actEv C B d = fiberMass C B d := by
  constructor
  · unfold r2RealPay r2Sia
    apply sum_realFiber_eq_of_hStar obs actEv C B d hH
    intro q hq h0
    subst hq
    simp only [dite_true, transport_rfl]
    exact forcedBelow_eq_zero_of_reach_eq_zero C B q a h0
  · unfold r2RealMass fiberMass
    exact sum_realFiber_eq_of_hStar obs actEv C B d hH _ (fun _ _ h => h)

/-- **R2-real (reading 1) = R2-SIA under `H*`** as well: the two readings coincide at every
`H*` point (dp-sl-2-058's "agree at Definition-7-recorded points", sharpened to `H*`).
Source: dp-sl-2-058 reading 1
Kind: P
Fidelity: exact
Hyps: (a) `HStar obs actEv C B d` -/
theorem r2RealAll_eq_r2Sia_of_hStar (hH : HStar obs actEv C B d) (a : acts d) :
    r2RealAllPay actEv C B d a = r2Sia C B d a ∧ r2RealAllMass actEv C B d = fiberMass C B d := by
  constructor
  · unfold r2RealAllPay r2Sia
    apply sum_realFiberAll_eq_of_hStar obs actEv C B d hH
    intro q hq h0
    subst hq
    simp only [dite_true, transport_rfl]
    exact forcedBelow_eq_zero_of_reach_eq_zero C B q a h0
  · unfold r2RealAllMass fiberMass
    exact sum_realFiberAll_eq_of_hStar obs actEv C B d hH _ (fun _ _ h => h)

end hstar

/-! ## T3(b′): under `RecordsFor` for `C` alone, EV = R2-real (reading 2)

Audit r1 (fidelity §3.2) observed that the reading-2 averaging set is already pinned down by
Definition 7 recording for `C`: an active `d`-node is subtree-veridical (clause 2) and a.s.
node-action-veridical (clause 3 on every positive leaf below it, all of which are `O_d`-leaves),
and a subtree-veridical `d`-node of positive reach is active. So `realFiber` and `svFiber` carry
the same sums, and the `H*` argument for R2-SIA goes through for R2-real without `H*`'s second
clause. R2-SIA itself still needs `H*` (`prop13_r2Sia_refuted_recordsFor_alone`), and so does
reading 1 (`mugRec_readings_differ`). -/

section recordsForReal

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
variable (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)

/-- Under recording for `C`, an active `d`-node is subtree-veridical and a.s.
node-action-veridical (`active_sv_nav_of_hStar` used only `H*`'s first clause).
Source: [[decision-problems-v2]] Definition 7 clauses 2–3
Kind: L -/
theorem active_sv_nav_of_recordsFor (hrec : RecordsFor obs actEv C B d) (q : B.DecNode)
    (hq : pt B q = d) (hact : ActiveNode obs C B d q) :
    SubtreeVeridical obs B q ∧ NodeActionVeridicalAS actEv C B q := by
  obtain ⟨ℓ₀, hpos₀, hobs₀, he₀⟩ := hact
  obtain ⟨a₀, ha₀⟩ := Option.isSome_iff_exists.mp he₀
  have hsv := ((hrec ℓ₀ hpos₀ hobs₀).2 q hq a₀ ha₀).1
  refine ⟨hsv, fun ℓ a hpos ha => ?_⟩
  have hobs : world B ℓ ∈ obs d := by
    have := hsv ℓ ((mem_leavesBelow B q ℓ).mpr (by rw [ha]; rfl))
    rwa [hq] at this
  exact ((hrec ℓ hpos hobs).2 q hq a ha).2.1

/-- A subtree-veridical `d`-node of positive reach is active: a positive leaf below it is a
positive `O_d`-leaf meeting it.
Source: none: infrastructure
Kind: L -/
theorem active_of_sv_of_reach_ne_zero (q : B.DecNode) (hq : pt B q = d)
    (hsv : SubtreeVeridical obs B q) (hr : reach C B q ≠ 0) : ActiveNode obs C B d q := by
  by_contra hna
  apply hr
  rw [reach_eq_zero_iff]
  intro ℓ he
  by_contra hne
  have hpos : 0 < leafLaw C B ℓ := (leafLaw_nonneg C B ℓ).lt_of_ne (Ne.symm hne)
  have hobs : world B ℓ ∈ obs d := by
    have := hsv ℓ ((mem_leavesBelow B q ℓ).mpr he)
    rwa [hq] at this
  exact hna ⟨ℓ, hpos, hobs, he⟩

/-- Under recording for `C`, the reading-2 fiber and the subtree-veridical fiber carry the same
sums for any `f` vanishing at reach `0`.
Source: dp-sl-2-058 (reading 2); audit r1 fidelity §3.2
Kind: L -/
theorem sum_realFiber_eq_sum_svFiber_of_recordsFor (hrec : RecordsFor obs actEv C B d)
    (f : B.DecNode → K) (hf : ∀ q, pt B q = d → reach C B q = 0 → f q = 0) :
    ∑ q ∈ realFiber obs actEv C B d, f q = ∑ q ∈ svFiber obs B d, f q := by
  apply Finset.sum_subset
  · intro q hq
    obtain ⟨hpt, -, hact⟩ := (mem_realFiber obs actEv C B d q).mp hq
    exact (mem_svFiber obs B d q).mpr
      ⟨hpt, (active_sv_nav_of_recordsFor obs actEv C B d hrec q hpt hact).1⟩
  · intro q hq hnot
    obtain ⟨hpt, hsv⟩ := (mem_svFiber obs B d q).mp hq
    apply hf q hpt
    by_contra hr
    have hact := active_of_sv_of_reach_ne_zero obs C B d q hpt hsv hr
    exact hnot ((mem_realFiber obs actEv C B d q).mpr
      ⟨hpt, (active_sv_nav_of_recordsFor obs actEv C B d hrec q hpt hact).2, hact⟩)

/-- **T3(b′), payoff mass**: under recording for `C` alone,
`∑_{λ ⊨ a ∧ O_d} μ_C(ℓ) r(ℓ) = C(d)(a) · r2RealPay(a)` (reading 2).
Source: `sl-defensible-claims.md` S1 (Proposition 13, R2-real clause), strengthened: the
source puts this clause under `H*`; dp-sl-2-061 (i) (its R2-real clause confirmed under
reading 2); audit r1 fidelity §3.2
Kind: P
Fidelity: stronger: `RecordsFor` for `C` in place of `H*` (reading 2 only)
Hyps: (a) `RecordsFor obs actEv C B d` -/
theorem paySum_actEv_inter_obs_eq_mul_r2Real (hrec : RecordsFor obs actEv C B d) (a : acts d) :
    paySum C B (actEv d a ∩ obs d) = (C d).w a * r2RealPay obs actEv C B d a := by
  rw [paySum_actEv_inter_obs_eq_sum_svFiber obs actEv C B d hrec a]
  unfold r2RealPay
  rw [Finset.mul_sum, sum_realFiber_eq_sum_svFiber_of_recordsFor obs actEv C B d hrec _
    (fun q hq h0 => by
      subst hq
      simp only [dite_true, transport_rfl]
      rw [forcedBelow_eq_zero_of_reach_eq_zero C B q a h0, mul_zero])]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hpt := ((mem_svFiber obs B d q).mp hq).1
  subst hpt
  simp only [dite_true, transport_rfl, edgeS_eq_some_iff]
  exact edge_paySum_eq_mul_forcedBelow C B q a

/-- **T3(b′), normaliser**: under recording for `C` alone, `ν_C(O_d) = r2RealMass` (reading 2).
Source: `sl-defensible-claims.md` S1 (Proposition 13), strengthened; audit r1 fidelity §3.2
Kind: P
Fidelity: stronger: `RecordsFor` for `C` in place of `H*`
Hyps: (a) `RecordsFor obs actEv C B d` -/
theorem nu_obs_eq_r2RealMass (hrec : RecordsFor obs actEv C B d) :
    nu C B (obs d) = r2RealMass obs actEv C B d := by
  have h1 : nu C B (obs d) = ∑ q ∈ svFiber obs B d, reach C B q := by
    rw [nu_eq_sum, Finset.sum_congr rfl (fun ℓ _ => ind_obs_eq_sum_svFiber obs actEv C B hrec ℓ),
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => sum_isSome_eq_reach C B q
  rw [h1]
  unfold r2RealMass
  exact (sum_realFiber_eq_sum_svFiber_of_recordsFor obs actEv C B d hrec _ (fun _ _ h => h)).symm

/-- **Proposition 13(b′): EV = R2-real (reading 2) under `RecordsFor` for `C` alone**,
cross-multiplied: `paySum_C(a ∧ O_d) · r2RealMass = r2RealPay(a) · ν_C(a ∧ O_d)`. The source
states the R2-real clause under `H*`; under the reading of record it needs only Definition 7
recording for `C`, like the R1-state clause. (R2-SIA does need `H*`:
`prop13_r2Sia_refuted_recordsFor_alone`; reading 1 does too: `mugRec_readings_differ`.)
Source: `sl-defensible-claims.md` S1 line 20 (Proposition 13, the R2-real clause),
strengthened; dp-sl-2-061 (i); audit r1 fidelity §3.2
Kind: C
Fidelity: stronger: `RecordsFor` for `C` in place of `H*`; variant: construal — R2-real read as
reading 2 (disclosed in `Defs.lean`)
Hyps: (a) `RecordsFor obs actEv C B d`; (c) reading 2 -/
theorem prop13_ev_eq_r2Real_of_recordsFor (hrec : RecordsFor obs actEv C B d) (a : acts d) :
    paySum C B (actEv d a ∩ obs d) * r2RealMass obs actEv C B d =
      r2RealPay obs actEv C B d a * nu C B (actEv d a ∩ obs d) := by
  rw [paySum_actEv_inter_obs_eq_mul_r2Real obs actEv C B d hrec a,
    nu_actEv_inter_obs_of_recordsFor obs actEv C B hrec a, nu_obs_eq_r2RealMass obs actEv C B d hrec]
  ring

end recordsForReal

/-! ## T1(c): post-query screening at a recorded `O_d = ⊤` point -/

section postQuery

variable (actEv : (d : ι) → acts d → Finset Ω)
variable (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)

/-- Dropping a positivity indicator under a non-negative summand.
Source: none: infrastructure
Kind: L -/
theorem sum_ite_pos_and (P : B.Leaves → Prop) [DecidablePred P] :
    (∑ ℓ, if 0 < leafLaw C B ℓ ∧ P ℓ then leafLaw C B ℓ else 0) =
      ∑ ℓ, if P ℓ then leafLaw C B ℓ else 0 := by
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hzero
  · simp [hpos]
  · rw [← hzero]; simp

/-- At an `O_d = ⊤` recorded point, `ν(X ∧ a)` is the sum over the fiber of the `X`-restricted
`a`-edge masses.
Source: none: infrastructure
Kind: L -/
theorem nu_inter_actEv_eq_sum_edgeMassIn (obs : ι → Finset Ω) (hO : obs d = Finset.univ)
    (hrec : RecordsFor obs actEv C B d) (X : Finset Ω) (a : acts d) :
    nu C B (X ∩ actEv d a) =
      ∑ q ∈ fiber B d, if h : pt B q = d then edgeMassIn C B X q (transport h.symm a) else 0 := by
  have h := nu_inter_actEv_eq_sum_fiber obs actEv hrec X a
  rw [hO, Finset.inter_univ] at h
  rw [h]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hpt := (Finset.mem_filter.mp hq).2
  subst hpt
  simp only [dite_true, transport_rfl, Finset.mem_univ, true_and, edgeS_eq_some_iff]
  unfold edgeMassIn
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases hc : edgeOf B q ℓ = some a ∧ world B ℓ ∈ X
  · rw [if_pos hc]
    rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hzero
    · rw [if_pos ⟨hpos, hc.2, hc.1⟩]
    · rw [← hzero]; simp
  · rw [if_neg hc, if_neg]
    rintro ⟨-, hX, he⟩
    exact hc ⟨he, hX⟩

/-- **Post-query screening at a recorded `O_d = ⊤` point**: if `B` records at `d` for `C` and
the event `X` is post-query independent of the draw at every `d`-node (`PostQueryIndep`), then
`ν(X ∧ a) · ν(b) = ν(X ∧ b) · ν(a)` for all actions `a, b`. This is the `k`-clause of the
repaired Lemma 3 in its general form: the lesion-only clause of (S1) is used only through the
per-node proportionality, and recording is what makes the world's act coordinate the draw.
Source: [[decision-problems-v2]] §7.3 Lemma 3 ("`m ⊥ (ℓ, k)` under `ν_{B,C}` for every `C`"),
repaired; `sl-synthesis.md` §1.3 ("Lemma 3's conclusion about `k` needs (S1)'s lesion-only
clause"); mandate T1(c)
Kind: P
Fidelity: exact (cross-multiplied); the hypothesis on post-query chance is the weakest found
(`PostQueryIndep`), weaker than `LesionOnlyAt`
Hyps: (a) `RecordsFor` for `C` at `O_d = ⊤`; (a) `PostQueryIndep C B d X` (a tree predicate,
implied by `LesionOnlyAt`) -/
theorem postQuery_screening_recorded (obs : ι → Finset Ω) (hO : obs d = Finset.univ)
    (hrec : RecordsFor obs actEv C B d) (X : Finset Ω) (hX : PostQueryIndep C B d X)
    (a b : acts d) :
    nu C B (X ∩ actEv d a) * nu C B (actEv d b) = nu C B (X ∩ actEv d b) * nu C B (actEv d a) := by
  -- the act masses: `ν(a) = C(d)(a) · W` with `W = ∑_q R_q`
  have hact : ∀ c : acts d, nu C B (actEv d c) = (C d).w c * ∑ q ∈ fiber B d, reach C B q := by
    intro c
    have h := nu_inter_actEv_eq_sum_edgeMassIn actEv C B d obs hO hrec Finset.univ c
    rw [Finset.univ_inter] at h
    rw [h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hpt := (Finset.mem_filter.mp hq).2
    subst hpt
    simp only [dite_true, transport_rfl]
    unfold edgeMassIn
    simp only [Finset.mem_univ, and_true]
    rw [← sum_isSome_eq_reach C B q]
    exact mass_edge C B q c
  -- the per-node identity `kIn(q, a) · C(d)(b) = kIn(q, b) · C(d)(a)`
  have hnode : ∀ q ∈ fiber B d, ∀ h : pt B q = d,
      edgeMassIn C B X q (transport h.symm a) * (C d).w b =
        edgeMassIn C B X q (transport h.symm b) * (C d).w a := by
    intro q hq h
    have hpq := hX q h (transport h.symm a) (transport h.symm b)
    subst h
    simp only [transport_rfl] at hpq ⊢
    unfold edgeMass at hpq
    rw [mass_edge C B q, mass_edge C B q, sum_isSome_eq_reach C B q] at hpq
    rcases (reach_nonneg C B q).lt_or_eq with hr | hr
    · have : (edgeMassIn C B X q a * (C (pt B q)).w b - edgeMassIn C B X q b * (C (pt B q)).w a)
          * reach C B q = 0 := by linear_combination hpq
      rcases mul_eq_zero.mp this with h0 | h0
      · linear_combination h0
      · exact absurd h0 hr.ne'
    · have hz : ∀ c, edgeMassIn C B X q c = 0 := by
        intro c
        unfold edgeMassIn
        apply Finset.sum_eq_zero
        intro ℓ _
        split_ifs with hc
        · exact (reach_eq_zero_iff C B q).mp hr.symm ℓ (by rw [hc.1]; rfl)
        · rfl
      rw [hz, hz]; ring
  rw [nu_inter_actEv_eq_sum_edgeMassIn actEv C B d obs hO hrec X a,
    nu_inter_actEv_eq_sum_edgeMassIn actEv C B d obs hO hrec X b, hact a, hact b]
  have key : (∑ q ∈ fiber B d, if h : pt B q = d then edgeMassIn C B X q (transport h.symm a)
        else 0) * (C d).w b =
      (∑ q ∈ fiber B d, if h : pt B q = d then edgeMassIn C B X q (transport h.symm b)
        else 0) * (C d).w a := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q hq => ?_
    by_cases h : pt B q = d
    · simp only [h, dite_true]
      exact hnode q hq h
    · simp [h]
  calc (∑ q ∈ fiber B d, if h : pt B q = d then edgeMassIn C B X q (transport h.symm a) else 0) *
        ((C d).w b * ∑ q ∈ fiber B d, reach C B q)
      = ((∑ q ∈ fiber B d, if h : pt B q = d then edgeMassIn C B X q (transport h.symm a)
          else 0) * (C d).w b) * ∑ q ∈ fiber B d, reach C B q := by ring
    _ = ((∑ q ∈ fiber B d, if h : pt B q = d then edgeMassIn C B X q (transport h.symm b)
          else 0) * (C d).w a) * ∑ q ∈ fiber B d, reach C B q := by rw [key]
    _ = _ := by ring

/-- **The `k`-clause of the repaired Lemma 3, general form**: at a recorded `O_d = ⊤` point
with cancer post-query independent of the draw, the act-conditionals of cancer under `ν` are
flat.
Source: [[decision-problems-v2]] §7.3 Lemma 3, repaired (`sl-synthesis.md` §1.3: "under
(S1)+(S3)+(S4) `m ⊥ (ℓ, k)` under `ν_{B,C}` for every `C`"); mandate T1(c)
Kind: C
Fidelity: exact (the `k`-clause; the `ℓ`-clause is `screening_recorded` with `X = evL`)
Hyps: (a) `RecordsFor slObs slActEv C B d`; (a) `PostQueryIndep C B d evK` -/
theorem nuFlat_of_recordsFor_postQueryIndep {ι' : Type} [DecidableEq ι']
    (C : Proc ι' (fun _ => Bool) K) (B : Tree TickleW ι' (fun _ => Bool) K) (d : ι')
    (hrec : RecordsFor slObs slActEv C B d) (hK : PostQueryIndep C B d evK) : NuFlat C B := by
  unfold NuFlat
  have := postQuery_screening_recorded slActEv C B d slObs rfl hrec evK hK true false
  simpa using this

end postQuery

end Cleanroom.Decision.DpSmokingLesion
