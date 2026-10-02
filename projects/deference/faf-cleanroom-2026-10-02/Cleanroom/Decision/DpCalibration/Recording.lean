import Cleanroom.Decision.DpCalibration.Basic
import Cleanroom.Found.DpCoreTree.Recording
import Cleanroom.Found.DpCoreTree.RecordingThms
import Cleanroom.Found.DpCoreTree.NodeSums
import Cleanroom.Found.DpCoreTree.Bernstein

/-!
# Recording: self-transparency, Proposition 7, CA-12′

T5 and T15(d) of [[dp-calibration-mandate]].

* `nu_actEv_inter_obs_of_recordsFor` — **the recording argument** (v2 Remark 3.6, reused by
  Proposition 7): under `RecordsFor obs actEv C B d`, `ν(a ∧ O_d) = C(d)(a) · ν(O_d)`. Route: a
  positive `O_d`-leaf lies in the action event `a` iff its unique `d`-node took the `a`-edge
  (clauses (1), (3), (4)); every `d`-node met by a positive `O_d`-run is subtree-veridical
  (clause (2)), so summing `dp-core-tree`'s edge-mass identity (`mass_edge`) over the
  subtree-veridical `d`-nodes gives both sides.
* `selfTransparent_of_recordsFor_strict` — recording + `0 < ν(O_d)` + strict OC at `d` ⟹
  self-transparency; `selfCertain_of_deterministic` — the deterministic corollary (Remark 3.6).
* `prop7_rigidity` — **Proposition 7**: two recorded procedures, both strictly calibrated at
  `d` with positive `ν(O_d)`, agree at `d`.
* `nu_factor_of_recordsForAll` / `paySum_factor_of_recordsForAll` — **CA-12′**: under
  `RecordsForAll obs actEv B d`, `ν_C(X ∧ a ∧ O_d) = C(d)(a) · Θ_C(X)` with `Θ` a function of
  `C` off `d` only (the `offWeight` factorisation of `Bernstein.lean` at a unique `d`-draw),
  hence the cross-multiplied independence `ca12_nu_cross`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-- The subtree-veridical `d`-nodes of `B` (a `C`-free set: subtree-veridicality quantifies over
*all* leaves below the node).
Source: [[decision-problems-v2]] §3.1 Definition 7 clause (2); Proposition 7 proof
Kind: D -/
noncomputable def svFiber (obs : ι → Finset Ω) (B : Tree Ω ι acts K) (d : ι) :
    Finset B.DecNode := by
  classical exact Finset.univ.filter fun q => pt B q = d ∧ SubtreeVeridical obs B q

/-- Membership in `svFiber`. Source: none: infrastructure. Kind: L -/
theorem mem_svFiber (obs : ι → Finset Ω) (B : Tree Ω ι acts K) (d : ι) (q : B.DecNode) :
    q ∈ svFiber obs B d ↔ pt B q = d ∧ SubtreeVeridical obs B q := by
  unfold svFiber
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

section recording

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
variable (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- Under recording, a positive `O_d`-leaf has exactly one `d`-node on its path, and that node
is subtree-veridical.
Source: [[decision-problems-v2]] Definition 7 clauses (1)–(2)
Kind: L -/
theorem dNodesOn_eq_singleton_of_recordsFor {d : ι} (h : RecordsFor obs actEv C B d)
    {ℓ : B.Leaves} (hpos : 0 < leafLaw C B ℓ) (hobs : world B ℓ ∈ obs d) :
    ∃ q₀, dNodesOn B d ℓ = {q₀} ∧ q₀ ∈ svFiber obs B d := by
  have h1 := (h ℓ hpos hobs).1
  rw [count_eq_card_dNodesOn, Finset.card_eq_one] at h1
  obtain ⟨q₀, hq₀⟩ := h1
  refine ⟨q₀, hq₀, ?_⟩
  have hmem : q₀ ∈ dNodesOn B d ℓ := by rw [hq₀]; exact Finset.mem_singleton_self q₀
  rw [mem_dNodesOn] at hmem
  obtain ⟨hpt, hsome⟩ := hmem
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hsome
  rw [mem_svFiber]
  exact ⟨hpt, ((h ℓ hpos hobs).2 q₀ hpt a ha).1⟩

/-- **The pointwise identity with an event inserted**: for every leaf, the indicator of
`λ(ℓ) ⊨ X ∧ a ∧ O_d` (weighted by `μ(ℓ)`) equals the sum over subtree-veridical `d`-nodes of
the indicator "the path took the `a`-edge at that node and `λ(ℓ) ⊨ X`".
Source: [[decision-problems-v2]] Proposition 7 proof ("action-veridicality with the
only-via-the-draw clause")
Kind: P -/
theorem ind_actEv_eq_sum_svFiber {d : ι} (h : RecordsFor obs actEv C B d) (a : acts d)
    (X : Finset Ω) (ℓ : B.Leaves) :
    (if world B ℓ ∈ X ∧ world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d then leafLaw C B ℓ else 0) =
      ∑ q ∈ svFiber obs B d,
        (if edgeS B q ℓ = some ⟨d, a⟩ ∧ world B ℓ ∈ X then leafLaw C B ℓ else 0) := by
  rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hzero
  · by_cases hobs : world B ℓ ∈ obs d
    · obtain ⟨q₀, hq₀, hsv⟩ := dNodesOn_eq_singleton_of_recordsFor obs actEv C B h hpos hobs
      have hmem : q₀ ∈ dNodesOn B d ℓ := by rw [hq₀]; exact Finset.mem_singleton_self q₀
      rw [mem_dNodesOn] at hmem
      obtain ⟨hpt, hsome⟩ := hmem
      -- only `q₀` contributes on the right
      rw [Finset.sum_eq_single q₀]
      · subst hpt
        obtain ⟨a₀, ha₀⟩ := Option.isSome_iff_exists.mp hsome
        obtain ⟨_, hact, huniq⟩ := (h ℓ hpos hobs).2 q₀ rfl a₀ ha₀
        simp only [edgeS_eq_some_iff, ha₀, Option.some.injEq]
        by_cases hE : a = a₀
        · subst hE
          simp [hact, hobs]
        · have hnot : world B ℓ ∉ actEv (pt B q₀) a := fun hc => hE (huniq a hc)
          simp [hnot, Ne.symm hE]
      · intro q _ hq
        have : ¬ (edgeS B q ℓ = some ⟨d, a⟩ ∧ world B ℓ ∈ X) := by
          rintro ⟨he, -⟩
          have hq' : q ∈ dNodesOn B d ℓ := by
            rw [mem_dNodesOn]
            exact ⟨pt_eq_of_edgeS B q ℓ he, isSome_of_edgeS B q ℓ he⟩
          rw [hq₀, Finset.mem_singleton] at hq'
          exact hq hq'
        simp [this]
      · intro hq; exact absurd hsv hq
    · have hL : ¬ (world B ℓ ∈ X ∧ world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d) :=
        fun hc => hobs hc.2.2
      rw [if_neg hL]
      symm
      apply Finset.sum_eq_zero
      intro q hq
      rw [mem_svFiber] at hq
      have : ¬ (edgeS B q ℓ = some ⟨d, a⟩ ∧ world B ℓ ∈ X) := by
        rintro ⟨he, -⟩
        have hbelow : ℓ ∈ leavesBelow B q := (mem_leavesBelow B q ℓ).mpr (isSome_of_edgeS B q ℓ he)
        have := hq.2 ℓ hbelow
        rw [hq.1] at this
        exact hobs this
      simp [this]
  · rw [← hzero]; simp

/-- **The pointwise identity for the observation alone**: the `μ`-weighted indicator of
`λ(ℓ) ⊨ O_d` is the sum over subtree-veridical `d`-nodes of the indicator "the path passes
that node".
Source: [[decision-problems-v2]] Proposition 7 proof ("`{λ ⊨ O_d}` coincide[s] a.s. with reaching
the unique `d`-node")
Kind: P -/
theorem ind_obs_eq_sum_svFiber {d : ι} (h : RecordsFor obs actEv C B d) (ℓ : B.Leaves) :
    (if world B ℓ ∈ obs d then leafLaw C B ℓ else 0) =
      ∑ q ∈ svFiber obs B d, (if (edgeOf B q ℓ).isSome then leafLaw C B ℓ else 0) := by
  rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hzero
  · by_cases hobs : world B ℓ ∈ obs d
    · obtain ⟨q₀, hq₀, hsv⟩ := dNodesOn_eq_singleton_of_recordsFor obs actEv C B h hpos hobs
      have hmem : q₀ ∈ dNodesOn B d ℓ := by rw [hq₀]; exact Finset.mem_singleton_self q₀
      rw [mem_dNodesOn] at hmem
      rw [Finset.sum_eq_single q₀]
      · simp [hobs, hmem.2]
      · intro q hq' hq
        have : ¬ (edgeOf B q ℓ).isSome := by
          intro he
          have hq'' : q ∈ dNodesOn B d ℓ := by
            rw [mem_dNodesOn]; exact ⟨((mem_svFiber obs B d q).mp hq').1, he⟩
          rw [hq₀, Finset.mem_singleton] at hq''
          exact hq hq''
        simp [this]
      · intro hq; exact absurd hsv hq
    · rw [if_neg hobs]
      symm
      apply Finset.sum_eq_zero
      intro q hq
      rw [mem_svFiber] at hq
      have : ¬ (edgeOf B q ℓ).isSome := by
        intro he
        have hbelow : ℓ ∈ leavesBelow B q := (mem_leavesBelow B q ℓ).mpr he
        have := hq.2 ℓ hbelow
        rw [hq.1] at this
        exact hobs this
      simp [this]
  · rw [← hzero]; simp

/-- `dp-core-tree`'s edge-mass identity in tagged-edge form: at a `d`-node `q`, the mass of the
leaves taking edge `⟨d, a⟩` is `C(d)(a)` times the mass of the leaves below `q`.
Source: [[decision-problems-v2]] §3.1 Definition 6 (`dp-core-tree`'s `mass_edge`)
Kind: L -/
theorem mass_edgeS {d : ι} (q : B.DecNode) (hq : pt B q = d) (a : acts d) :
    (∑ ℓ, if edgeS B q ℓ = some ⟨d, a⟩ then leafLaw C B ℓ else 0) =
      (C d).w a * ∑ ℓ, if (edgeOf B q ℓ).isSome then leafLaw C B ℓ else 0 := by
  subst hq
  simp only [edgeS_eq_some_iff]
  exact mass_edge C B q a

/-- **The recording argument** (Remark 3.6; the lemma Proposition 7 reuses): if `B` records at
`d` for `C`, then `ν_{B,C}(a ∧ O_d) = C(d)(a) · ν_{B,C}(O_d)` for every action `a` of `d`.
Source: [[decision-problems-v2]] §3.1 Remark 3.6 ("`ν(a ∣ O_d) = C(d)(a)` (the recording
argument, reused in Proposition 7)"); Proposition 7 proof
Kind: P
Fidelity: exact (cross-multiplied; no positivity needed for the identity itself)
Hyps: (a) `RecordsFor obs actEv C B d` (`dp-core-tree`'s Definition 7) -/
theorem nu_actEv_inter_obs_of_recordsFor {d : ι} (h : RecordsFor obs actEv C B d)
    (a : acts d) :
    nu C B (actEv d a ∩ obs d) = (C d).w a * nu C B (obs d) := by
  have hL : nu C B (actEv d a ∩ obs d) =
      ∑ ℓ, if world B ℓ ∈ Finset.univ ∧ world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d
        then leafLaw C B ℓ else 0 := by
    rw [nu_eq_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp [Finset.mem_inter]
  have hR : nu C B (obs d) = ∑ q ∈ svFiber obs B d,
      ∑ ℓ, if (edgeOf B q ℓ).isSome then leafLaw C B ℓ else 0 := by
    rw [nu_eq_sum, Finset.sum_congr rfl (fun ℓ _ => ind_obs_eq_sum_svFiber obs actEv C B h ℓ),
      Finset.sum_comm]
  rw [hL, Finset.sum_congr rfl
      (fun ℓ _ => ind_actEv_eq_sum_svFiber obs actEv C B h a Finset.univ ℓ),
    Finset.sum_comm, hR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  simp only [Finset.mem_univ, and_true]
  exact mass_edgeS C B q ((mem_svFiber obs B d q).mp hq).1 a

/-- **Self-transparency from recording and strict calibration** (T5(c)): if `B` records at `d`
for `C`, `0 < ν(O_d)` and the strict clauses hold at `d`, then `P_{s_d}(a) = C(d)(a)` for all
`a`.
Source: [[decision-problems-v2]] §3.1 Remark 3.6; Appendix B item 2
Kind: C
Fidelity: exact
Hyps: (a) recording (Definition 7), (a) `0 < ν(O_d)`, (a) strict OC at `d` -/
theorem selfTransparent_of_recordsFor_strict (s : ι → State Ω K) {d : ι}
    (h : RecordsFor obs actEv C B d) (hpos : 0 < nu C B (obs d))
    (hs : StrictOCAt s obs C B d) : SelfTransparent s actEv C d := by
  intro a
  have h1 := (hs hpos).1 (actEv d a)
  rw [nu_actEv_inter_obs_of_recordsFor obs actEv C B h a] at h1
  exact mul_right_cancel₀ hpos.ne' h1

/-- **Remark 3.6, forced self-knowledge**: for a deterministic `C(d) = δ_{a₀}`, recording,
`0 < ν(O_d)` and strict OC at `d` force `P_{s_d}(a₀) = 1` and `P_{s_d}(a) = 0` for every other
action.
Source: [[decision-problems-v2]] §3.1 Remark 3.6 ("clause 1 forces `P_{s_d}(C(d)) = 1`")
Kind: C
Fidelity: exact
Hyps: (a) recording, (a) positivity, (a) strict OC at `d`, (a) `C d = δ_{a₀}` -/
theorem selfCertain_of_deterministic (s : ι → State Ω K) {d : ι} (a₀ : acts d)
    (hC : C d = FinDistr.pure a₀) (h : RecordsFor obs actEv C B d) (hpos : 0 < nu C B (obs d))
    (hs : StrictOCAt s obs C B d) :
    (s d).pr (actEv d a₀) = 1 ∧ ∀ a, a ≠ a₀ → (s d).pr (actEv d a) = 0 := by
  have hst := selfTransparent_of_recordsFor_strict obs actEv C B s h hpos hs
  constructor
  · rw [hst a₀, hC]; simp
  · intro a ha
    rw [hst a, hC]; simp [ha]

/-- **`A_d^+ = {C(d)}`** under the hypotheses of Remark 3.6 (the domain collapse behind
Remark 3.9's theorem-let; T6).
Source: [[decision-problems-v2]] §3.1 Remark 3.9 ("`A_d^+ = {C(d)}`")
Kind: C
Fidelity: exact — stated *per point* with `0 < ν(O_d)` (v2's remark omits the positivity; see
findings)
Hyps: (a) recording, (a) positivity, (a) strict OC at `d`, (a) `C d = δ_{a₀}` -/
theorem aPlus_eq_singleton_of_deterministic (s : ι → State Ω K) {d : ι} (a₀ : acts d)
    (hC : C d = FinDistr.pure a₀) (h : RecordsFor obs actEv C B d) (hpos : 0 < nu C B (obs d))
    (hs : StrictOCAt s obs C B d) : APlus s actEv d = {a₀} := by
  obtain ⟨h1, h0⟩ := selfCertain_of_deterministic obs actEv C B s a₀ hC h hpos hs
  ext a
  simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro ha
    by_contra hne
    rw [h0 a hne] at ha
    exact lt_irrefl _ ha
  · rintro rfl; rw [h1]; exact one_pos

/-- **Proposition 7 (rigidity of strict calibration)**: if `B` records at `d` for both `C` and
`C'`, both are strictly calibrated at `d` (same state assignment `s`), and `ν_C(O_d) > 0`,
`ν_{C'}(O_d) > 0`, then `C(d) = C'(d)`.
Source: [[decision-problems-v2]] §6 Proposition 7
Kind: C
Fidelity: exact
Hyps: (a) recording for `C` and for `C'` (Definition 7), (a) both positivities, (a) strict OC
at `d` for both (the mandate's LB 5) -/
theorem prop7_rigidity (s : ι → State Ω K) {d : ι} (C' : Proc ι acts K)
    (h : RecordsFor obs actEv C B d) (h' : RecordsFor obs actEv C' B d)
    (hpos : 0 < nu C B (obs d)) (hpos' : 0 < nu C' B (obs d))
    (hs : StrictOCAt s obs C B d) (hs' : StrictOCAt s obs C' B d) : C d = C' d := by
  have t := selfTransparent_of_recordsFor_strict obs actEv C B s h hpos hs
  have t' := selfTransparent_of_recordsFor_strict obs actEv C' B s h' hpos' hs'
  apply FinDistr.ext'
  intro a
  rw [← t a, ← t' a]

/-- Proposition 7 stated with `RecordsForAll` (the weaker-looking form the mandate allows).
Source: [[decision-problems-v2]] §6 Proposition 7
Kind: L -/
theorem prop7_rigidity_of_recordsForAll (s : ι → State Ω K) {d : ι} (C' : Proc ι acts K)
    (hall : RecordsForAll obs actEv B d)
    (hpos : 0 < nu C B (obs d)) (hpos' : 0 < nu C' B (obs d))
    (hs : StrictOCAt s obs C B d) (hs' : StrictOCAt s obs C' B d) : C d = C' d :=
  prop7_rigidity obs actEv C B s C' (hall C) (hall C') hpos hpos' hs hs'

/-- **Strict ⟹ masked (LF) when the strict state's action credences are full-support and the
point is recorded**: the self-model `m := C(d)` is then full-support (self-transparency) and
`C[d ↦ C(d)] = C`, so the strict clauses are the masked clauses.
Source: [[decision-problems-v2]] Remark 3.7 ("its fixed point is strict calibration"); mandate T10
Kind: C
Fidelity: exact
Hyps: (a) recording, (a) positivity, (a) strict OC at `d`, (a) `∀ a, 0 < P_{s_d}(a)` -/
theorem maskedOCAt_of_strict_fullSupport (s : ι → State Ω K) {d : ι}
    (h : RecordsFor obs actEv C B d) (hpos : 0 < nu C B (obs d))
    (hs : StrictOCAt s obs C B d) (hfull : ∀ a, 0 < (s d).pr (actEv d a)) :
    MaskedOCAt s obs C B d := by
  have t := selfTransparent_of_recordsFor_strict obs actEv C B s h hpos hs
  have hdev : C.deviate d (C d) = C := Function.update_eq_self d C
  refine Or.inl ⟨C, ⟨C d, fun a => ?_, hdev.symm⟩, hpos, hs hpos⟩
  rw [← t a]; exact hfull a

end recording

/-! ## CA-12′: under recording for every procedure, the act values at `d` do not depend on `C(d)` -/

section ca12

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω) (B : Tree Ω ι acts K)

/-- The uniform procedure (full support at every point), used to transfer "chance-positive"
into "positive under some procedure".
Source: none: infrastructure
Kind: D -/
def uniformProc [∀ d, Nonempty (acts d)] : Proc ι acts K := fun _ => FinDistr.uniform

/-- Under the uniform procedure every chance-positive leaf has positive mass.
Source: none: infrastructure
Kind: L -/
theorem leafLaw_uniformProc_pos [∀ d, Nonempty (acts d)] :
    (T : Tree Ω ι acts K) → ∀ ℓ, 0 < chanceWeight T ℓ → 0 < leafLaw (uniformProc (K := K)) T ℓ
  | Tree.leaf _ _, _, _ => one_pos
  | Tree.chance _ β child, ⟨i, ℓ⟩, h => by
      simp only [chanceWeight_chance] at h
      simp only [leafLaw_chance]
      have hi : 0 < β.w i := by
        rcases (β.nonneg i).lt_or_eq with hi | hi
        · exact hi
        · rw [← hi, zero_mul] at h; exact absurd h (lt_irrefl 0)
      have hrest : 0 < chanceWeight (child i) ℓ := by
        rcases (chanceWeight_nonneg (child i) ℓ).lt_or_eq with hc | hc
        · exact hc
        · rw [← hc, mul_zero] at h; exact absurd h (lt_irrefl 0)
      exact mul_pos hi (leafLaw_uniformProc_pos (child i) ℓ hrest)
  | Tree.decision d child, ⟨a, ℓ⟩, h => by
      simp only [chanceWeight_decision] at h
      simp only [leafLaw_decision]
      exact mul_pos (FinDistr.uniform_w_pos a) (leafLaw_uniformProc_pos (child a) ℓ h)

/-- A leaf with a single `d`-draw, which is `⟨d, a⟩`: its draw list filtered to `d` is
`[⟨d, a⟩]`.
Source: none: infrastructure
Kind: L -/
theorem filter_draws_eq_singleton {d : ι} {a : acts d} {ℓ : B.Leaves}
    (h1 : count d B ℓ = 1) (hmem : (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ) :
    (draws B ℓ).filter (fun x => x.1 = d) = [⟨d, a⟩] := by
  have hlen : ((draws B ℓ).filter (fun x => x.1 = d)).length = 1 := by
    rw [length_filter_draws]; exact h1
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
  have : (⟨d, a⟩ : Σ d, acts d) ∈ (draws B ℓ).filter (fun x => x.1 = d) :=
    List.mem_filter.mpr ⟨hmem, by simp⟩
  rw [hx, List.mem_singleton] at this
  rw [hx, this]

/-- **The single-draw factorisation**: at a leaf with exactly one `d`-node, which took the
`a`-edge, `μ_C(ℓ) = C(d)(a) · offWeight_C(ℓ)`.
Source: [[decision-problems-v2]] Proposition 4 proof (the pattern decomposition, at `k = 1`);
`calibration.md` CA-12′ ("`ν(a ∧ O_d ∧ X) = ∑_q R_q C(d)(a) θ_{q,a}(X)`")
Kind: P -/
theorem leafLaw_eq_w_mul_offWeight (C : Proc ι acts K) {d : ι} {a : acts d} {ℓ : B.Leaves}
    (h1 : count d B ℓ = 1) (hmem : (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ) :
    leafLaw C B ℓ = (C d).w a * offWeight C d B ℓ := by
  rw [leafLaw_eq_chanceWeight_mul_drawsWeight, drawsWeight, offWeight,
    prod_map_filter_split d, filter_draws_eq_singleton B h1 hmem]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  ring

/-- `Θ_C(a, X)`: the total off-`d` weight of the leaves below subtree-veridical `d`-nodes that
take the `a`-edge with `λ(ℓ) ⊨ X`. A function of `C` off `d` only (`theta_congr_off`).
Source: `calibration.md` CA-12′ (`∑_q R_q θ_{q,a}(X)`)
Kind: D -/
noncomputable def theta (C : Proc ι acts K) (d : ι) (a : acts d) (X : Finset Ω) : K :=
  ∑ q ∈ svFiber obs B d,
    ∑ ℓ, if edgeS B q ℓ = some ⟨d, a⟩ ∧ world B ℓ ∈ X then offWeight C d B ℓ else 0

/-- The payoff-weighted `Θ`. Source: `calibration.md` CA-12′. Kind: D -/
noncomputable def thetaPay (C : Proc ι acts K) (d : ι) (a : acts d) (X : Finset Ω) : K :=
  ∑ q ∈ svFiber obs B d,
    ∑ ℓ, if edgeS B q ℓ = some ⟨d, a⟩ ∧ world B ℓ ∈ X
      then offWeight C d B ℓ * payoff B ℓ else 0

/-- `offWeight` depends on `C` off `d` only. Source: none: infrastructure. Kind: L -/
theorem offWeight_congr_off {C C' : Proc ι acts K} (d : ι) (hoff : ∀ d', d' ≠ d → C d' = C' d')
    (ℓ : B.Leaves) : offWeight C d B ℓ = offWeight C' d B ℓ := by
  unfold offWeight
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro x hx
  have := List.of_mem_filter hx
  simp only [decide_eq_true_eq] at this
  rw [hoff x.1 this]

/-- `Θ` depends on `C` off `d` only. Source: `calibration.md` CA-12′. Kind: L -/
theorem theta_congr_off {C C' : Proc ι acts K} (d : ι) (hoff : ∀ d', d' ≠ d → C d' = C' d')
    (a : acts d) (X : Finset Ω) : theta obs B C d a X = theta obs B C' d a X := by
  unfold theta
  simp only [offWeight_congr_off B d hoff]

/-- `Θ^r` depends on `C` off `d` only. Source: `calibration.md` CA-12′. Kind: L -/
theorem thetaPay_congr_off {C C' : Proc ι acts K} (d : ι) (hoff : ∀ d', d' ≠ d → C d' = C' d')
    (a : acts d) (X : Finset Ω) : thetaPay obs B C d a X = thetaPay obs B C' d a X := by
  unfold thetaPay
  simp only [offWeight_congr_off B d hoff]

/-- Under recording for every procedure, every chance-positive leaf below a subtree-veridical
`d`-node taking the `a`-edge is a single-`d`-draw leaf with draw `⟨d, a⟩`, so
`μ_C(ℓ) = C(d)(a) · offWeight_C(ℓ)` for **every** `C`.
Source: `calibration.md` CA-12′ ("two `d`-nodes on an `O_d`-run are excluded for every
procedure")
Kind: P -/
theorem leafLaw_factor_of_recordsForAll [∀ d, Nonempty (acts d)] {d : ι}
    (hall : RecordsForAll obs actEv B d) (C : Proc ι acts K) {q : B.DecNode}
    (hq : q ∈ svFiber obs B d) {a : acts d} {ℓ : B.Leaves}
    (he : edgeS B q ℓ = some ⟨d, a⟩) :
    leafLaw C B ℓ = (C d).w a * offWeight C d B ℓ := by
  rcases (chanceWeight_nonneg B ℓ).lt_or_eq with hc | hc
  · -- chance-positive: positive under the uniform procedure, hence a recorded `O_d`-run
    have hU := leafLaw_uniformProc_pos (K := K) B ℓ hc
    rw [mem_svFiber] at hq
    have hobs : world B ℓ ∈ obs d := by
      have := hq.2 ℓ ((mem_leavesBelow B q ℓ).mpr (isSome_of_edgeS B q ℓ he))
      rwa [hq.1] at this
    have h1 := (hall (uniformProc (K := K)) ℓ hU hobs).1
    have hmem : (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ :=
      (mem_draws_iff_exists_edgeS B ℓ ⟨d, a⟩).mpr ⟨q, he⟩
    exact leafLaw_eq_w_mul_offWeight B C h1 hmem
  · -- chance-null: both sides vanish
    rw [leafLaw_eq_chanceWeight_mul_drawsWeight, offWeight, ← hc]; ring

/-- **CA-12′, the factorisation**: under recording for every procedure,
`ν_C(X ∧ a ∧ O_d) = C(d)(a) · Θ_C(a, X)` with `Θ_C` a function of `C` off `d`.
Source: `cf-workflow/phase2-notes/repair/calibration.md` CA-12′
Kind: P
Fidelity: exact
Hyps: (a) `RecordsForAll obs actEv B d` (the hypothesis CA-12′ was repaired to) -/
theorem nu_factor_of_recordsForAll [∀ d, Nonempty (acts d)] {d : ι}
    (hall : RecordsForAll obs actEv B d) (C : Proc ι acts K) (a : acts d) (X : Finset Ω) :
    nu C B (X ∩ actEv d a ∩ obs d) = (C d).w a * theta obs B C d a X := by
  have hL : nu C B (X ∩ actEv d a ∩ obs d) =
      ∑ ℓ, if world B ℓ ∈ X ∧ world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d
        then leafLaw C B ℓ else 0 := by
    rw [nu_eq_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp [Finset.mem_inter]
  rw [hL, Finset.sum_congr rfl
      (fun ℓ _ => ind_actEv_eq_sum_svFiber obs actEv C B (hall C) a X ℓ),
    Finset.sum_comm, theta, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  split_ifs with hcond
  · exact leafLaw_factor_of_recordsForAll obs actEv B hall C hq hcond.1
  · ring

/-- **CA-12′ for the payoff sums**: `∑_{λ ⊨ X ∧ a ∧ O_d} μ_C r = C(d)(a) · Θ^r_C(a, X)`.
Source: `calibration.md` CA-12′ ("likewise for the payoff sums")
Kind: P
Fidelity: exact
Hyps: (a) `RecordsForAll obs actEv B d` -/
theorem paySum_factor_of_recordsForAll [∀ d, Nonempty (acts d)] {d : ι}
    (hall : RecordsForAll obs actEv B d) (C : Proc ι acts K) (a : acts d) (X : Finset Ω) :
    paySum C B (X ∩ actEv d a ∩ obs d) = (C d).w a * thetaPay obs B C d a X := by
  have hL : paySum C B (X ∩ actEv d a ∩ obs d) =
      ∑ ℓ, (if world B ℓ ∈ X ∧ world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d
        then leafLaw C B ℓ else 0) * payoff B ℓ := by
    rw [paySum_eq_sum_ite]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    by_cases hc : world B ℓ ∈ X ∩ actEv d a ∩ obs d
    · have hc' : world B ℓ ∈ X ∧ world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d := by
        simpa [Finset.mem_inter, and_assoc] using hc
      simp [hc']
    · have hc' : ¬ (world B ℓ ∈ X ∧ world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d) := by
        simpa [Finset.mem_inter, and_assoc] using hc
      simp [hc']
  rw [hL, Finset.sum_congr rfl
      (fun ℓ _ => by rw [ind_actEv_eq_sum_svFiber obs actEv C B (hall C) a X ℓ]),
    thetaPay, Finset.mul_sum]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  split_ifs with hcond
  · rw [leafLaw_factor_of_recordsForAll obs actEv B hall C hq hcond.1]; ring
  · ring

/-- **CA-12′, cross-multiplied**: under recording for every procedure, for `C, C'` agreeing off
`d`, `ν_C(X ∧ a ∧ O_d) · ν_{C'}(a ∧ O_d) = ν_{C'}(X ∧ a ∧ O_d) · ν_C(a ∧ O_d)` — the strict
act-conditional at `d` does not depend on `C(d)`.
Source: `calibration.md` CA-12′ ("the act values at `d` are `C(d)`-independent")
Kind: C
Fidelity: exact
Hyps: (a) `RecordsForAll obs actEv B d`, (a) `C`, `C'` agree off `d` -/
theorem ca12_nu_cross [∀ d, Nonempty (acts d)] {d : ι} (hall : RecordsForAll obs actEv B d)
    {C C' : Proc ι acts K} (hoff : ∀ d', d' ≠ d → C d' = C' d') (a : acts d) (X : Finset Ω) :
    nu C B (X ∩ actEv d a ∩ obs d) * nu C' B (Finset.univ ∩ actEv d a ∩ obs d) =
      nu C' B (X ∩ actEv d a ∩ obs d) * nu C B (Finset.univ ∩ actEv d a ∩ obs d) := by
  rw [nu_factor_of_recordsForAll obs actEv B hall C a X,
    nu_factor_of_recordsForAll obs actEv B hall C' a X,
    nu_factor_of_recordsForAll obs actEv B hall C a Finset.univ,
    nu_factor_of_recordsForAll obs actEv B hall C' a Finset.univ,
    theta_congr_off obs B d hoff a X, theta_congr_off obs B d hoff a Finset.univ]
  ring

/-- **CA-12′ for the payoff side**: the strict act *value* at `d` does not depend on `C(d)`.
Source: `calibration.md` CA-12′
Kind: C
Fidelity: exact
Hyps: (a) `RecordsForAll obs actEv B d`, (a) `C`, `C'` agree off `d` -/
theorem ca12_paySum_cross [∀ d, Nonempty (acts d)] {d : ι}
    (hall : RecordsForAll obs actEv B d) {C C' : Proc ι acts K}
    (hoff : ∀ d', d' ≠ d → C d' = C' d') (a : acts d) (X : Finset Ω) :
    paySum C B (X ∩ actEv d a ∩ obs d) * nu C' B (X ∩ actEv d a ∩ obs d) =
      paySum C' B (X ∩ actEv d a ∩ obs d) * nu C B (X ∩ actEv d a ∩ obs d) := by
  rw [paySum_factor_of_recordsForAll obs actEv B hall C a X,
    paySum_factor_of_recordsForAll obs actEv B hall C' a X,
    nu_factor_of_recordsForAll obs actEv B hall C a X,
    nu_factor_of_recordsForAll obs actEv B hall C' a X,
    theta_congr_off obs B d hoff a X, thetaPay_congr_off obs B d hoff a X]
  ring

end ca12

end Cleanroom.Decision.DpCalibration
