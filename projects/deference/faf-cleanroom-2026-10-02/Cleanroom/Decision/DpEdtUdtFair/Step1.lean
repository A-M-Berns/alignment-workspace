import Cleanroom.Decision.DpEdtUdtFair.FairClass

/-!
# Step 1 of FR-11: the conditioning event is "reach a `d`-node and draw `a`", and the act value
is `Q` (T2)

On `𝔉`, for every full-support procedure `C'` (in particular every tremble `C^ε`, `ε > 0`) and
every queried `d`:

* **the set identity** (dp-cf-119's static core, `FairClass.mem_actEv_inter_obs_iff`): a leaf's
  world satisfies `a ∧ O_d` iff its path draws `⟨d, a⟩` at some `d`-node — recording supplies
  both directions on positive leaves (all leaves are positive: pruned + full support), and
  fiber propagation of subtree-veridicality (`FairClass.subtreeVeridical`) supplies the
  observation clause at every `d`-node, not only the recorded one (`adversary-repair.md` A.2:
  `FRec` alone does not give it);
* **the reach weights cancel** (`sum_drew_eq`): by structural recursion, when every `d`-subtree
  is labelled-isomorphic to the reference `decision d c₀` and `#_d ≤ 1`, the `⟨d, a⟩`-draw mass
  of any `(λ, r)`-functional is `C(d)(a) · fiberMass_d(C) · ∫ g dμ_{c₀ a, C}`;
* hence `ν_{C'}(a ∧ O_d) = C'(d)(a) · fiberMass_d(C')`, `∑_{λ ⊨ a ∧ O_d} μ_{C'} r = C'(d)(a) ·
  fiberMass_d(C') · Q_{C'}(d, a)`, and for `C'(d)(a) > 0` the calibrated act value
  `𝔼_{C'}[r ∣ a ∧ O_d]` **is** `Q_{C'}(d, a)` (`FairClass.condExp_eq_Q`).

Also: on `𝔉`, `occ(d)` is exactly the `O_d`-runs (`FairClass.mem_occ_iff`), so `H_d` holds for
every procedure and `dp-calibration`'s ZO-2 chain applies with no extra hypothesis.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpEdtUdtFair

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt
open Cleanroom.Decision.DpCalibration

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-! ### Draw sets and the fiber mass -/

section drew

omit [Fintype Ω] [DecidableEq Ω] in
/-- A tagged edge `some ⟨e, b⟩` at `q` carries `q`'s point.
Source: none: infrastructure
Kind: L -/
theorem pt_eq_of_edgeS_eq_some {B : Tree Ω ι acts K} {q : B.DecNode} {ℓ : B.Leaves}
    {x : Σ d, acts d} (h : edgeS B q ℓ = some x) : pt B q = x.1 := by
  unfold edgeS at h
  cases h' : edgeOf B q ℓ with
  | none => rw [h'] at h; cases h
  | some b =>
      rw [h'] at h
      change some (⟨pt B q, b⟩ : Σ d, acts d) = some x at h
      rw [← Option.some.inj h]

omit [Fintype Ω] [DecidableEq Ω] in
/-- A path drawing `⟨d, a⟩` meets `d`.
Source: none: infrastructure
Kind: L -/
theorem count_pos_of_mem_draws {B : Tree Ω ι acts K} {d : ι} {a : acts d} {ℓ : B.Leaves}
    (h : (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ) : 0 < count d B ℓ := by
  obtain ⟨q, hq⟩ := (mem_draws_iff_exists_edgeS B ℓ _).mp h
  have hpt : pt B q = d := pt_eq_of_edgeS_eq_some hq
  have := count_pos_of_edge B q ℓ (isSome_of_edgeS B q ℓ hq)
  rwa [hpt] at this

variable (C : Proc ι acts K)

omit [Fintype Ω] [DecidableEq Ω] in
/-- The fiber mass vanishes where no path meets `d`.
Source: none: infrastructure
Kind: L -/
theorem fiberMass_eq_zero_of_count_eq_zero {B : Tree Ω ι acts K} (d : ι)
    (h : ∀ ℓ, count d B ℓ = 0) : fiberMass C B d = 0 := by
  unfold fiberMass
  rw [sum_reach_fiber_eq_expCount]
  unfold Tree.expCount
  exact Finset.sum_eq_zero fun ℓ _ => by rw [h ℓ]; simp

omit [Fintype Ω] [DecidableEq Ω] in
/-- **The reach weights cancel** (FR-11 Step 1's identity, for any `(λ, r)`-functional `g`): when
every `d`-subtree of `B` is labelled-isomorphic to `decision d c₀` and no path meets `d` twice,
`∑_{ℓ : ⟨d,a⟩ ∈ draws ℓ} μ_C(ℓ) g(λ(ℓ), r(ℓ)) = C(d)(a) · fiberMass_d(C) · ∫ g dμ_{c₀ a, C}`.
By structural recursion: at a `d`-node the `a`-child contributes `C(d)(a) · ∫ g dμ_{child a}`,
equal to the reference by `LabIso.contLaw_eq`, and no `d`-node lies below it; elsewhere the
recursion of `fiberMass` is matched term by term.
Source: `fair-repair.md` FR-11 Step 1 ("the reach-weights … multiply a constant and cancel");
`adversary-repair.md` Claim A Step 1
Kind: P
Fidelity: exact -/
theorem sum_drew_eq (d : ι) (a : acts d) (c₀ : acts d → Tree Ω ι acts K) (g : Ω × K → K) :
    (B : Tree Ω ι acts K) →
      (∀ q : B.DecNode, pt B q = d → LabIso (subtreeAt B q) (.decision d c₀)) →
      (∀ ℓ, count d B ℓ ≤ 1) →
      (∑ ℓ, if (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ then
          leafLaw C B ℓ * g (world B ℓ, payoff B ℓ) else 0) =
        (C d).w a * (fiberMass C B d * lawInt C (c₀ a) g)
  | leaf _ _, _, _ => by simp [fiberMass_leaf]
  | chance _ β child, hT, hc => by
      have ih : ∀ i, (∑ ℓ, if (⟨d, a⟩ : Σ d, acts d) ∈ draws (child i) ℓ then
          leafLaw C (child i) ℓ * g (world (child i) ℓ, payoff (child i) ℓ) else 0) =
          (C d).w a * (fiberMass C (child i) d * lawInt C (c₀ a) g) := fun i =>
        sum_drew_eq d a c₀ g (child i) (fun q hq => hT ⟨i, q⟩ hq)
          (fun ℓ => by simpa using hc ⟨i, ℓ⟩)
      rw [sum_leaves_chance, fiberMass_chance, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      calc (∑ ℓ, if (⟨d, a⟩ : Σ d, acts d) ∈ draws (chance _ β child) ⟨i, ℓ⟩ then
              leafLaw C (chance _ β child) ⟨i, ℓ⟩ *
                g (world (chance _ β child) ⟨i, ℓ⟩, payoff (chance _ β child) ⟨i, ℓ⟩) else 0)
            = β.w i * ∑ ℓ, (if (⟨d, a⟩ : Σ d, acts d) ∈ draws (child i) ℓ then
                leafLaw C (child i) ℓ * g (world (child i) ℓ, payoff (child i) ℓ) else 0) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun ℓ _ => ?_
              simp only [draws_chance, leafLaw_chance, world_chance, payoff_chance]
              split_ifs <;> ring
        _ = (C d).w a * (β.w i * fiberMass C (child i) d * lawInt C (c₀ a) g) := by
              rw [ih i]; ring
  | decision d' child, hT, hc => by
      have ih : ∀ b, (∑ ℓ, if (⟨d, a⟩ : Σ d, acts d) ∈ draws (child b) ℓ then
          leafLaw C (child b) ℓ * g (world (child b) ℓ, payoff (child b) ℓ) else 0) =
          (C d).w a * (fiberMass C (child b) d * lawInt C (c₀ a) g) := fun b =>
        sum_drew_eq d a c₀ g (child b) (fun q hq => hT (some ⟨b, q⟩) hq)
          (fun ℓ => by have := hc ⟨b, ℓ⟩; simp only [count_decision] at this; omega)
      rw [sum_leaves_decision, fiberMass_decision]
      by_cases hd : d' = d
      · subst hd
        -- no `d'`-node below the root: every child's fiber mass vanishes
        have hzero : ∀ b, fiberMass C (child b) d' = 0 := fun b =>
          fiberMass_eq_zero_of_count_eq_zero C d' fun ℓ => by
            have := hc ⟨b, ℓ⟩; simp only [count_decision, if_true] at this; omega
        have hiso : LabIso (Tree.decision d' child) (Tree.decision d' c₀) := by
          simpa using hT none rfl
        have hval : lawInt C (child a) g = lawInt C (c₀ a) g := by
          cases hiso with
          | decision _ _ _ hchild => exact lawInt_eq_of_contLaw_eq C ((hchild a).contLaw_eq C) g
        simp only [hzero, mul_zero, Finset.sum_const_zero, add_zero, if_true, one_mul]
        rw [Finset.sum_eq_single a]
        · rw [← hval]
          unfold lawInt
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          simp only [draws_decision, List.mem_cons, true_or, if_true, leafLaw_decision,
            world_decision, payoff_decision]
          ring
        · intro b _ hb
          apply Finset.sum_eq_zero
          intro ℓ _
          rw [if_neg]
          simp only [draws_decision, List.mem_cons, not_or]
          refine ⟨fun heq => hb (eq_of_heq (Sigma.mk.inj_iff.mp heq).2).symm, fun hmem => ?_⟩
          have h1 := count_pos_of_mem_draws hmem
          have h2 := hc ⟨b, ℓ⟩
          simp only [count_decision, if_true] at h2
          omega
        · intro h; exact absurd (Finset.mem_univ a) h
      · simp only [if_neg hd, zero_add]
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        calc (∑ ℓ, if (⟨d, a⟩ : Σ d, acts d) ∈ draws (decision d' child) ⟨b, ℓ⟩ then
                leafLaw C (decision d' child) ⟨b, ℓ⟩ *
                  g (world (decision d' child) ⟨b, ℓ⟩, payoff (decision d' child) ⟨b, ℓ⟩) else 0)
              = (C d').w b * ∑ ℓ, (if (⟨d, a⟩ : Σ d, acts d) ∈ draws (child b) ℓ then
                  leafLaw C (child b) ℓ * g (world (child b) ℓ, payoff (child b) ℓ) else 0) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun ℓ _ => ?_
                have hne : ¬ ((⟨d, a⟩ : Σ d, acts d) = ⟨d', b⟩) :=
                  fun heq => hd (Sigma.mk.inj_iff.mp heq).1.symm
                simp only [draws_decision, List.mem_cons, hne, false_or, leafLaw_decision,
                  world_decision, payoff_decision]
                split_ifs <;> ring
          _ = (C d).w a * ((C d').w b * fiberMass C (child b) d * lawInt C (c₀ a) g) := by
                rw [ih b]; ring

end drew

/-! ### On `𝔉`: the set identity and the act values -/

section fair

variable {obs : ι → Finset Ω} {actEv : (d : ι) → acts d → Finset Ω}

/-- **The set identity (dp-cf-119's static core; Claim A Step 1)**: on `𝔉`, under a
full-support procedure, a leaf's world satisfies `a ∧ O_d` iff its path draws `⟨d, a⟩`. (→):
recording at the leaf (positive: pruned + full support) gives a unique `d`-node on the path
whose drawn act is the only act event the world satisfies. (←): the drawing node is
subtree-veridical (`FairClass.subtreeVeridical`), so the world satisfies `O_d`, and recording's
action-veridicality clause gives `a`.
Source: `fair-repair.md` FR-11 Step 1 ("`{λ ⊨ a ∧ O_d} = {runs reaching some q ∈ F_d and drawing
a}`"); `adversary-repair.md` Claim A Step 1; dp-cf-119
Kind: P
Fidelity: exact (every leaf, not only a.s.: all leaves are positive on `𝔉` under full support)
Hyps: (a) `FairClass`, (a) `C'` full support -/
theorem FairClass.mem_actEv_inter_obs_iff [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) {C' : Proc ι acts K} (hC' : C'.FullSupport) {d : ι}
    (hd : d ∈ queried B) (a : acts d) (ℓ : B.Leaves) :
    world B ℓ ∈ actEv d a ∩ obs d ↔ (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ := by
  have hlaw : 0 < leafLaw C' B ℓ := pruned_leafLaw_pos h.pruned hC' ℓ
  constructor
  · intro hw
    rw [Finset.mem_inter] at hw
    obtain ⟨hcount, hnodes⟩ := h.frec d hd C' ℓ hlaw hw.2
    obtain ⟨q, hq, hme⟩ := exists_dNode_of_count_pos d B ℓ (by omega)
    subst hq
    obtain ⟨a₀, ha₀⟩ := Option.isSome_iff_exists.mp hme
    obtain ⟨-, -, huniq⟩ := hnodes q rfl a₀ ha₀
    have haa : a = a₀ := huniq a hw.1
    subst haa
    exact (mem_draws_iff_exists_edgeS B ℓ _).mpr ⟨q, (edgeS_eq_some_iff B q ℓ a).mpr ha₀⟩
  · intro hmem
    obtain ⟨q, hq⟩ := (mem_draws_iff_exists_edgeS B ℓ _).mp hmem
    have hpt : pt B q = d := pt_eq_of_edgeS_eq_some hq
    subst hpt
    have he : edgeOf B q ℓ = some a := (edgeS_eq_some_iff B q ℓ a).mp hq
    have hobs : world B ℓ ∈ obs (pt B q) :=
      h.subtreeVeridical hd q rfl ℓ ((mem_leavesBelow B q ℓ).mpr (by rw [he]; rfl))
    obtain ⟨-, hnodes⟩ := h.frec _ hd C' ℓ hlaw hobs
    exact Finset.mem_inter.mpr ⟨(hnodes q rfl a he).2.1, hobs⟩

/-- The set identity in tagged-edge form: `λ(ℓ) ⊨ a ∧ O_d` iff some node `q` on the path has
`edgeS B q ℓ = some ⟨d, a⟩` (i.e. `q` carries `d` and the path takes its `a`-edge).
Source: dp-cf-119 (the extension of record: "`∀ ℓ, 0 < μ(ℓ) → (λ(ℓ) ⊨ a ∧ O_d ↔ ∃ q ∈ F_d,
edgeOf q ℓ = some a)`")
Kind: C -/
theorem FairClass.mem_actEv_inter_obs_iff_edgeS [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) {C' : Proc ι acts K} (hC' : C'.FullSupport) {d : ι}
    (hd : d ∈ queried B) (a : acts d) (ℓ : B.Leaves) :
    world B ℓ ∈ actEv d a ∩ obs d ↔ ∃ q : B.DecNode, edgeS B q ℓ = some ⟨d, a⟩ := by
  rw [h.mem_actEv_inter_obs_iff hC' hd a ℓ, mem_draws_iff_exists_edgeS]

/-- **`occ(d)` is the set of `O_d`-runs on `𝔉`** (every leaf; the a.s. form of Remark 3.4 with
no null set): coverage from recording, the converse from fiber propagation of
subtree-veridicality. This is `H_d` for every procedure, so `dp-calibration`'s ZO-2 chain
(`zo2_chain`) applies on `𝔉` with no extra hypothesis.
Source: `zoo.md` ZO-2 ("hence `occ(d) = {λ ⊨ O_d}` a.s. for every `C`"); v2 Remark 3.4
Kind: P
Fidelity: stronger: every leaf (pruned + full support make every leaf positive)
Hyps: (a) `FairClass`, (a) `C'` full support -/
theorem FairClass.mem_occ_iff [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) {C' : Proc ι acts K} (hC' : C'.FullSupport) {d : ι}
    (hd : d ∈ queried B) (ℓ : B.Leaves) : ℓ ∈ occ d B ↔ world B ℓ ∈ obs d := by
  rw [mem_occ]
  constructor
  · intro hc
    obtain ⟨q, hq, hme⟩ := exists_dNode_of_count_pos d B ℓ hc
    have := h.subtreeVeridical hd q hq ℓ ((mem_leavesBelow B q ℓ).mpr hme)
    rwa [hq] at this
  · intro hobs
    have := (h.frec d hd C' ℓ (pruned_leafLaw_pos h.pruned hC' ℓ) hobs).1
    omega

/-- On `𝔉` under a full-support procedure, the leaves whose world satisfies `a ∧ O_d` are
exactly the leaves drawing `⟨d, a⟩`.
Source: `fair-repair.md` FR-11 Step 1
Kind: L -/
theorem FairClass.worldEv_eq_drew [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) {C' : Proc ι acts K} (hC' : C'.FullSupport) {d : ι}
    (hd : d ∈ queried B) (a : acts d) : worldEv B (actEv d a ∩ obs d) = drew d a B := by
  ext ℓ
  simp only [worldEv, drew, Finset.mem_filter, Finset.mem_univ, true_and]
  exact h.mem_actEv_inter_obs_iff hC' hd a ℓ

/-- **`ν_{C'}(a ∧ O_d) = C'(d)(a) · fiberMass_d(C')`** on `𝔉` under full support: the recording
argument's `ν(O_d)` is the fiber mass (Step 1's "reach a `d`-node").
Source: `fair-repair.md` FR-11 Step 1–2; mandate T2(b)
Kind: P
Fidelity: exact
Hyps: (a) `FairClass`, (a) `C'` full support -/
theorem FairClass.nu_actEv_inter_obs_eq_fiberMass [∀ d, Nonempty (acts d)]
    {B : Tree Ω ι acts K} (h : FairClass obs actEv B) {C' : Proc ι acts K}
    (hC' : C'.FullSupport) {d : ι} (hd : d ∈ queried B) (a : acts d) :
    nu C' B (actEv d a ∩ obs d) = (C' d).w a * fiberMass C' B d := by
  unfold nu mass
  rw [h.worldEv_eq_drew hC' hd a]
  unfold drew
  rw [Finset.sum_filter]
  have key := sum_drew_eq C' d a (refChildren B d) (fun _ => 1) B
    (stronglyFair_iso_ref h.stronglyFair hd) (StronglyFair.almostFair B h.stronglyFair d)
  simp only [mul_one] at key
  rw [key]
  unfold lawInt
  simp only [mul_one, sum_leafLaw]

/-- On `𝔉` under full support, `ν_{C'}(O_d) = fiberMass_d(C')`.
Source: `fair-repair.md` FR-11 Step 1 (coverage + subtree-veridicality: `occ(d) = {λ ⊨ O_d}`)
Kind: C -/
theorem FairClass.nu_obs_eq_fiberMass [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) {C' : Proc ι acts K} (hC' : C'.FullSupport) {d : ι}
    (hd : d ∈ queried B) : nu C' B (obs d) = fiberMass C' B d := by
  obtain ⟨a⟩ := (inferInstance : Nonempty (acts d))
  have h1 := h.nu_actEv_inter_obs_eq_fiberMass hC' hd a
  rw [h.nu_actEv_inter_obs C' hd a] at h1
  exact mul_left_cancel₀ (hC' d a).ne' h1

/-- **The payoff mass of `a ∧ O_d` is `C'(d)(a) · fiberMass_d(C') · Q_{C'}(d, a)`** on `𝔉` under
full support (Step 1's cancellation, for the payoff functional).
Source: `fair-repair.md` FR-11 Step 1; mandate T2(b)
Kind: P
Fidelity: exact
Hyps: (a) `FairClass`, (a) `C'` full support -/
theorem FairClass.paySum_actEv_inter_obs_eq [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) {C' : Proc ι acts K} (hC' : C'.FullSupport) {d : ι}
    (hd : d ∈ queried B) (a : acts d) :
    paySum C' B (actEv d a ∩ obs d) = (C' d).w a * (fiberMass C' B d * Q C' B d a) := by
  unfold paySum
  rw [h.worldEv_eq_drew hC' hd a]
  unfold drew
  rw [Finset.sum_filter]
  exact sum_drew_eq C' d a (refChildren B d) Prod.snd B
    (stronglyFair_iso_ref h.stronglyFair hd) (StronglyFair.almostFair B h.stronglyFair d)

/-- **FR-11 Step 1 (Claim A Step 1, the act value)**: on `𝔉`, for every full-support `C'`, every
queried `d` and every `a` with `C'(d)(a) > 0`, the strictly calibrated act value
`𝔼_{C'}[r ∣ λ ⊨ a ∧ O_d]` equals the fiber-constant one-step deviation value `Q_{C'}(d, a)`.
The guard is real: at `C'(d)(a) = 0` the conditional is junk.
Source: `fair-repair.md` FR-11 Step 1 ("`V_{s^ε_d}(a) = 𝔼_{μ_ε}[r ∣ λ ⊨ a ∧ O_d] = … =
v_ε(d,a)`"); `adversary-repair.md` Claim A Step 1 [derived, verified]; A36 Lemma 4; CA-16′
Kind: P
Fidelity: exact
Hyps: (a) `FairClass`, (a) `C'` full support, (a) `0 < C'(d)(a)` -/
theorem FairClass.condExp_eq_Q [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) {C' : Proc ι acts K} (hC' : C'.FullSupport) {d : ι}
    (hd : d ∈ queried B) (a : acts d) (ha : 0 < (C' d).w a) :
    condExp C' B (actEv d a ∩ obs d) = Q C' B d a := by
  unfold condExp
  rw [h.paySum_actEv_inter_obs_eq hC' hd a, h.nu_actEv_inter_obs_eq_fiberMass hC' hd a,
    mul_div_mul_left _ _ ha.ne', mul_div_cancel_left₀ _ (h.fiberMass_pos hC' hd).ne']

end fair

end Cleanroom.Decision.DpEdtUdtFair
