import Cleanroom.Decision.DpFirstpersonSc.Audit

/-!
# FP-22′, the license to update (T2) and occurrence-expressibility (T3)

* `agree_calibratedState_jeffreyCond_iff` — on one carrier, the strictly calibrated state at `O`
  agrees with the prior state conditioned on `E` **iff** `ν(O △ E) = 0` (both halves named; the
  two inclusions are real: `⟸` is `mass_congr_ae` on the symmetric difference, `⟹` reads the
  two conditionals at `X := O` and `X := E`).
* **T2(a), FP-22′ on the stamped algebra** (`audit_license_iff_nullDiff`,
  `audit_license_iff_bridge`): the stamped strict-OC state passes the audit at `d` iff
  `μ(occ(d) ∖ λ⁻¹O_d) = 0 ∧ μ(λ⁻¹O_d ∖ occ(d)) = 0` — a.s. subtree-veridicality
  (`VeridicalASAt`) and a.s. coverage (`CoversAS`, which is `dp-core-tree`'s `Covers` exactly,
  `coversAS_iff_covers`) — i.e. Proposition 3's bridge `H_d` (`license_iff_bridge` via
  `dp-core-tree`'s `covers_and_veridical_iff`), i.e. "updating on `O_d` is licensed". Proposition
  3 itself is `dp-calibration`'s `perRunClausesAt_iff_strictClausesAt`; what is new is that the
  audit *measures* exactly the null-set form of its hypothesis. Grade `P`.
* **T2(b), the base algebra** (`auditBase_of_bridge`): under `H_d` the base strict-OC state
  passes the base audit (`⟸`, a composition of Proposition 3 and T1(a)); `⟹` is **refuted** on
  the coverage-failure tree (`WitnessesLicense.lean`).
* **T3(a)** (`perRunClausesAt_iff_strictClausesAt_of_nullDiff`): if `occ(d)` is a.s. a world
  event `λ⁻¹X` (`OccExpressible`), per-run SSC at `d` is strict OC at the relabelled point
  `(s_d, X, A_d)` — Proposition 3 is the case `X = O_d`. **T3(b), AN-3′'s exact criterion**
  (`occState_P_eq_nuCondDistr_iff`): the per-run state's `P` is a `ν`-conditional for *some*
  event iff the ratio `μ({λ = ω} ∩ occ(d)) / ν({ω})` is constant on the per-run support
  (multiplicative form). AN-3's converse ("non-expressible ⟹ not a `ν`-conditional") is dead
  (`anticipation.md` Dead 1) and is not stated.

Scope: finite regime, Definition 6; stamped headlines on `stamp U B` with `d ∈ U`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-! ## Null sets -/

section null

variable (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- A leaf set is null iff every leaf in it has zero law. Source: none: infrastructure. Kind: L -/
theorem mass_eq_zero_iff (S : Finset B.Leaves) :
    mass C B S = 0 ↔ ∀ ℓ ∈ S, leafLaw C B ℓ = 0 :=
  Finset.sum_eq_zero_iff_of_nonneg fun ℓ _ => leafLaw_nonneg C B ℓ

/-- A positive leaf has its world outside every `ν`-null event.
Source: none: infrastructure. Kind: L -/
theorem world_notMem_of_nu_eq_zero {Y : Finset Ω} (h : nu C B Y = 0) (ℓ : B.Leaves)
    (hpos : 0 < leafLaw C B ℓ) : world B ℓ ∉ Y := by
  intro hw
  have := (mass_eq_zero_iff C B _).mp h ℓ (by simp [worldEv, hw])
  exact hpos.ne' this

/-- `ν(E) = ν(E ∩ O) + ν(E ∖ O)`. Source: none: infrastructure. Kind: L -/
theorem nu_eq_inter_add_sdiff (E O : Finset Ω) :
    nu C B E = nu C B (E ∩ O) + nu C B (E \ O) := by
  have hU : E ∩ O ∪ E \ O = E := by
    ext ω
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  rw [← nu_union C B (Finset.disjoint_sdiff_inter E O).symm, hU]

end null

/-! ## Conditioning on a.s.-equal events -/

section oneCarrier

variable (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **Equal conditionals iff null symmetric difference**: the strictly calibrated state at `O`
agrees with the prior state Jeffrey-conditioned on `E` iff `ν(O ∖ E) = 0 ∧ ν(E ∖ O) = 0`.
Source: [[decision-problems-v2]] §3.1 Proposition 3 proof ("conditioning on equal events yields
equal conditionals"), Remark 3.10 (the symmetric difference); `firstperson.md` FP-22′
Kind: P
Fidelity: exact
Hyps: (a) `0 < ν(O)`, (a) `0 < ν(E)` -/
theorem agree_calibratedState_jeffreyCond_iff (O E : Finset Ω) (hO : 0 < nu C B O)
    (hE : 0 < (priorState C B).pr E) :
    State.Agree (calibratedState C B O hO) (jeffreyCond (priorState C B) E hE) ↔
      nu C B (O \ E) = 0 ∧ nu C B (E \ O) = 0 := by
  have hE' : 0 < nu C B E := by rwa [priorState_pr] at hE
  have hpr : ∀ X, (jeffreyCond (priorState C B) E hE).pr X = nu C B (X ∩ E) / nu C B E := by
    intro X; rw [jeffreyCond_pr, priorState_pr, priorState_pr]
  have hV : ∀ X, (jeffreyCond (priorState C B) E hE).V X =
      paySum C B (X ∩ E) / nu C B (X ∩ E) := by
    intro X; rw [jeffreyCond_V, priorState_V]
  constructor
  · intro hag
    have hP : ∀ X, nu C B (X ∩ O) / nu C B O = nu C B (X ∩ E) / nu C B E := by
      intro X
      have hPX : probOf (calibratedState C B O hO).P X =
          probOf (jeffreyCond (priorState C B) E hE).P X := by rw [hag.1]
      have h1 := calibratedState_pr C B O hO X
      have h2 := hpr X
      simp only [State.pr] at h1 h2
      rw [← h1, ← h2, hPX]
    constructor
    · have := hP E
      rw [Finset.inter_self, div_self hE'.ne', Finset.inter_comm, div_eq_one_iff_eq hO.ne'] at this
      have hsplit := nu_eq_inter_add_sdiff C B O E
      linarith
    · have := hP O
      rw [Finset.inter_self, div_self hO.ne', eq_comm, div_eq_one_iff_eq hE'.ne'] at this
      have hsplit := nu_eq_inter_add_sdiff C B E O
      rw [Finset.inter_comm] at hsplit
      linarith
  · rintro ⟨h1, h2⟩
    have hae : ∀ ℓ, 0 < leafLaw C B ℓ → (world B ℓ ∈ O ↔ world B ℓ ∈ E) := by
      intro ℓ hpos
      have n1 := world_notMem_of_nu_eq_zero C B h1 ℓ hpos
      have n2 := world_notMem_of_nu_eq_zero C B h2 ℓ hpos
      simp only [Finset.mem_sdiff, not_and, not_not] at n1 n2
      exact ⟨n1, n2⟩
    have hnu : ∀ X, nu C B (X ∩ O) = nu C B (X ∩ E) := by
      intro X
      unfold nu
      apply mass_congr_ae
      intro ℓ hpos
      simp only [worldEv, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
      rw [hae ℓ hpos]
    have hpay : ∀ X, paySum C B (X ∩ O) = paySum C B (X ∩ E) := by
      intro X
      unfold paySum
      apply paySumLeaves_congr_ae
      intro ℓ hpos
      simp only [worldEv, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
      rw [hae ℓ hpos]
    have hOE : nu C B O = nu C B E := by
      have a := hnu O
      have b := hnu E
      rw [Finset.inter_self] at a b
      rw [a, Finset.inter_comm, ← b]
    refine ⟨?_, fun X _ => ?_⟩
    · apply FinDistr.ext'
      intro ω
      have h1 := calibratedState_pr C B O hO {ω}
      have h2 := hpr {ω}
      simp only [State.pr, probOf_singleton] at h1 h2
      rw [h1, h2, hnu, hOE]
    · rw [calibratedState_V, hV, hnu, hpay]

end oneCarrier

/-! ## T2(a): the license on the stamped algebra -/

section license

variable (obs : ι → Finset Ω) (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)

/-- **A.s. subtree-veridicality at `d`, null-set form**: `μ(occ(d) ∖ {λ ⊨ O_d}) = 0` — no
positive-mass run is consulted at `d` in a world where `O_d` fails (`μ(¬O_d | occ(d)) = 0`).
Source: `firstperson.md` FP-22′ ("a.s. subtree-veridicality ⟺ `μ(¬O_d | occ(d)) = 0`")
Kind: D
Fidelity: exact (null-set form; equivalent to `∀ q, SubtreeVeridicalAS` jointly with coverage,
`license_iff_bridge`) -/
def VeridicalASAt : Prop := mass C B (occ d B \ worldEv B (obs d)) = 0

/-- **A.s. coverage at `d`, null-set form**: `μ({λ ⊨ O_d} ∖ occ(d)) = 0` — no positive-mass
`O_d`-run misses every `d`-node (`ν(pol_d = ⊥ | O_d) = 0`). Equals `dp-core-tree`'s `Covers`
(`coversAS_iff_covers`).
Source: `firstperson.md` FP-22′ ("coverage ⟺ `ν(pol_d = ⊥ | O_d) = 0`")
Kind: D
Fidelity: exact -/
def CoversAS : Prop := mass C B (worldEv B (obs d) \ occ d B) = 0

/-- **The license** (both null sets): `occ(d) △ λ⁻¹O_d` is `μ`-null.
Source: `firstperson.md` FP-22′ ("updating on `O_d` is licensed"); `anticipation.md` AN-8(iii)
Kind: D -/
def License : Prop := VeridicalASAt obs C B d ∧ CoversAS obs C B d

/-- Null-set coverage is Definition 7's coverage. Source: [[decision-problems-v2]] Definition 7.
Kind: L -/
theorem coversAS_iff_covers : CoversAS obs C B d ↔ Covers obs C B d := by
  unfold CoversAS Covers
  rw [mass_eq_zero_iff]
  constructor
  · intro h ℓ hpos hw
    by_contra hc
    rw [not_lt, Nat.le_zero] at hc
    have := h ℓ (by simp [worldEv, hw, hc])
    exact hpos.ne' this
  · intro h ℓ hℓ
    simp only [Finset.mem_sdiff, worldEv, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_occ, not_lt, Nat.le_zero] at hℓ
    by_contra hc
    have hpos : 0 < leafLaw C B ℓ := lt_of_le_of_ne (leafLaw_nonneg C B ℓ) (Ne.symm hc)
    have := h ℓ hpos hℓ.1
    omega

/-- **The license is Proposition 3's hypothesis `H_d`**: coverage and a.s. subtree-veridicality
at every `d`-node (`dp-core-tree`'s predicates), via Remark 3.4.
Source: [[decision-problems-v2]] §3.1 Proposition 3, Remark 3.4; `firstperson.md` FP-22′
Kind: L -/
theorem license_iff_bridge :
    License obs C B d ↔ (Covers obs C B d ∧ ∀ q, pt B q = d → SubtreeVeridicalAS obs C B q) := by
  rw [covers_and_veridical_iff]
  unfold License VeridicalASAt CoversAS
  rw [mass_eq_zero_iff, mass_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩ ℓ hpos
    constructor
    · intro hocc
      by_contra hw
      exact hpos.ne' (h1 ℓ (by simp [hocc, worldEv, hw]))
    · intro hw
      by_contra hocc
      exact hpos.ne' (h2 ℓ (by simp [worldEv, hw, hocc]))
  · intro h
    constructor
    · intro ℓ hℓ
      simp only [Finset.mem_sdiff, worldEv, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
      by_contra hc
      have hpos : 0 < leafLaw C B ℓ := lt_of_le_of_ne (leafLaw_nonneg C B ℓ) (Ne.symm hc)
      exact hℓ.2 ((h ℓ hpos).mp hℓ.1)
    · intro ℓ hℓ
      simp only [Finset.mem_sdiff, worldEv, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
      by_contra hc
      have hpos : 0 < leafLaw C B ℓ := lt_of_le_of_ne (leafLaw_nonneg C B ℓ) (Ne.symm hc)
      exact hℓ.2 ((h ℓ hpos).mpr hℓ.1)

variable (U : Finset ι) (hd : d ∈ U)

/-- **T2(a), FP-22′ on the stamped algebra, null-set form**: the stamped strict-OC state at
`d` (calibrated at the base observation read on the stamped carrier) passes the audit against the
stamped prior with evidence `occ(d)` **iff** `μ(occ(d) ∖ λ⁻¹O_d) = 0 ∧ μ(λ⁻¹O_d ∖ occ(d)) = 0`.
Source: `firstperson.md` FP-22′ ("On `𝓔^U` … audit-pass at `d` ⟺ Prop 3's bridge at `d` a.s.");
`anticipation.md` AN-8(iii) ("passes iff `occ(d) △ λ⁻¹O_d` is `μ`-null")
Kind: P
Fidelity: exact (stamped algebra; no `AlmostFair` needed — `occW` is `{#_d > 0}` on every tree)
Hyps: (a) `0 < ν(O_d)`, (a) `0 < μ(occ(d))` -/
theorem audit_license_iff_nullDiff (hO : 0 < nu C (stamp U B) (obsW U (obs d)))
    (h : 0 < (priorState C (stamp U B)).pr (occW U hd)) :
    AuditPassAt (priorState C (stamp U B)) (occW U hd) h id
        (calibratedState C (stamp U B) (obsW U (obs d)) hO) ↔
      License obs C B d := by
  rw [auditPassAt_id_iff, auditRef, agree_calibratedState_jeffreyCond_iff,
    nu_stamp_obsW_sdiff_occW, nu_stamp_occW_sdiff_obsW]
  unfold License VeridicalASAt CoversAS
  exact and_comm

/-- **T2(a), FP-22′ as the license to update**: the stamped strict-OC state passes the audit at
`d` iff Proposition 3's bridge holds at `d` (coverage and a.s. subtree-veridicality at every
`d`-node) — iff updating on `O_d` is licensed, the per-run and strict clauses being then one
equation (`perRunClausesAt_iff_strictClausesAt`).
Source: `firstperson.md` FP-22′; [[decision-problems-v2]] Proposition 3
Kind: C
Fidelity: exact
Hyps: (a) `0 < ν(O_d)`, (a) `0 < μ(occ(d))` -/
theorem audit_license_iff_bridge (hO : 0 < nu C (stamp U B) (obsW U (obs d)))
    (h : 0 < (priorState C (stamp U B)).pr (occW U hd)) :
    AuditPassAt (priorState C (stamp U B)) (occW U hd) h id
        (calibratedState C (stamp U B) (obsW U (obs d)) hO) ↔
      (Covers obs C B d ∧ ∀ q, pt B q = d → SubtreeVeridicalAS obs C B q) := by
  rw [audit_license_iff_nullDiff, license_iff_bridge]

/-- **T2(b), the base algebra, `⟸`**: under `H_d` the base strict-OC state passes the base
audit (the audit against the stamped prior read through `Prod.fst`): Proposition 3 composed with
T1(a). The converse `⟹` is refuted (`WitnessesLicense.lean`, `coverFail`).
Source: `firstperson.md` FP-22′ ("On the base algebra `𝓔` only `⟸`")
Kind: C
Fidelity: exact
Hyps: (a) `H_d`, (a) `0 < ν(O_d)`, (a) `0 < μ(occ(d))` -/
theorem auditBase_of_bridge (hcov : Covers obs C B d)
    (hver : ∀ q, pt B q = d → SubtreeVeridicalAS obs C B q) (hO : 0 < nu C B (obs d))
    (h : 0 < (priorState C (stamp U B)).pr (occW U hd)) :
    AuditPassAt (priorState C (stamp U B)) (occW U hd) h Prod.fst
      (calibratedState C B (obs d) hO) := by
  have := (audit_iff_perRunClausesAt C B U hd (fun _ => calibratedState C B (obs d) hO) h).mpr
  apply this
  rw [perRunClausesAt_iff_strictClausesAt obs C B _ hcov hver]
  exact strictClausesAt_calibratedState obs C B _ d hO rfl

end license

/-! ## T3: occurrence-expressibility and AN-3′ -/

section expressible

variable (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)

/-- **Occurrence-expressibility** (AN-3): `occ(d)` is a.s. a world event `λ⁻¹X`.
Source: `anticipation.md` AN-3 ("if `occ(d) = λ⁻¹(Occ_d)` mod `μ`-null")
Kind: D -/
def OccExpressible : Prop :=
  ∃ X : Finset Ω, mass C B (occ d B \ worldEv B X) = 0 ∧ mass C B (worldEv B X \ occ d B) = 0

/-- **T3(a), AN-3**: if `occ(d)` is a.s. `λ⁻¹X`, per-run SSC at `d` is strict OC at the point
relabelled to the observation `X` — Proposition 3 is the case `X = O_d`.
Source: `anticipation.md` AN-3(i) ("both Def-13 per-run clauses at `d` coincide with both Def-8
clauses at `(s_d, Occ_d, A_d)`")
Kind: P
Fidelity: exact
Hyps: (a) `occ(d) △ λ⁻¹X` null -/
theorem perRunClausesAt_iff_strictClausesAt_of_nullDiff (s : ι → State Ω K) (X : Finset Ω)
    (h1 : mass C B (occ d B \ worldEv B X) = 0) (h2 : mass C B (worldEv B X \ occ d B) = 0) :
    PerRunClausesAt s C B d ↔ StrictClausesAt s (fun _ => X) C B d := by
  have hae : ∀ ℓ, 0 < leafLaw C B ℓ → (ℓ ∈ occ d B ↔ world B ℓ ∈ X) := by
    intro ℓ hpos
    rw [mass_eq_zero_iff] at h1 h2
    constructor
    · intro hocc
      by_contra hw
      exact hpos.ne' (h1 ℓ (by simp [hocc, worldEv, hw]))
    · intro hw
      by_contra hocc
      exact hpos.ne' (h2 ℓ (by simp [worldEv, hw, hocc]))
  have hnu : ∀ Y, mass C B (worldEv B Y ∩ occ d B) = nu C B (Y ∩ X) := by
    intro Y
    unfold nu
    apply mass_congr_ae
    intro ℓ hpos
    simp only [Finset.mem_inter, worldEv, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hae ℓ hpos]
  have hocc : mass C B (occ d B) = nu C B X := by
    have := hnu Finset.univ
    rwa [worldEv_univ, Finset.univ_inter, Finset.univ_inter] at this
  have hpay : ∀ Y, (∑ ℓ ∈ worldEv B Y ∩ occ d B, leafLaw C B ℓ * payoff B ℓ) =
      paySum C B (Y ∩ X) := by
    intro Y
    unfold paySum
    apply paySumLeaves_congr_ae
    intro ℓ hpos
    simp only [Finset.mem_inter, worldEv, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hae ℓ hpos]
  unfold PerRunClausesAt StrictClausesAt PerRunClause1At PerRunClause2At StrictClause1At
    StrictClause2At
  simp only [hnu, hocc, hpay]

/-- An occurrence-expressible point: per-run SSC at `d` is strict OC at *some* relabelling.
Source: `anticipation.md` AN-3 (takeaway)
Kind: L -/
theorem exists_strictClausesAt_of_occExpressible (s : ι → State Ω K) (h : OccExpressible C B d) :
    ∃ X : Finset Ω, (PerRunClausesAt s C B d ↔ StrictClausesAt s (fun _ => X) C B d) := by
  obtain ⟨X, h1, h2⟩ := h
  exact ⟨X, perRunClausesAt_iff_strictClausesAt_of_nullDiff C B d s X h1 h2⟩

/-- The per-run support: the worlds realized on some positive-mass occurrence run.
Source: `anticipation.md` AN-3′ ("the state's support")
Kind: D -/
def perRunSupport : Finset Ω := Finset.univ.filter fun ω => 0 < mass C B (occEv B d {ω})

/-- `μ({λ = ω} ∩ occ(d)) ≤ ν({ω})`. Source: none: infrastructure. Kind: L -/
theorem mass_occEv_singleton_le_nu (ω : Ω) : mass C B (occEv B d {ω}) ≤ nu C B {ω} :=
  mass_mono C B Finset.inter_subset_left

/-- `μ(occ(d)) = ∑_ω μ({λ = ω} ∩ occ(d))`, restricted to the per-run support.
Source: none: infrastructure. Kind: L -/
theorem mass_occ_eq_sum_support :
    mass C B (occ d B) = ∑ ω ∈ perRunSupport C B d, mass C B (occEv B d {ω}) := by
  rw [← occEv_univ B d, ← sum_mass_occEv_singleton]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro ω _ hω
  simp only [perRunSupport, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hω
  exact le_antisymm hω (mass_nonneg C B _)

/-- **T3(b), AN-3′'s exact criterion (`P`-clause)**: the per-run state's probability is
`ν(· | X)` for *some* event `X` iff the ratio `μ({λ = ω} ∩ occ(d)) / ν({ω})` is constant on the
per-run support — stated multiplicatively (`m(ω) ν(ω') = m(ω') ν(ω)` for `ω, ω'` in the
support). When it is, `X` is the support. This is the statistical test that decides Q3's "same
notion on a refined algebra" at the `P`-clause; non-expressibility decides nothing (AN-3's
converse is dead, `anticipation.md` Dead 1).
Source: `anticipation.md` AN-3′ ("the per-run SSC state equals `ν(· | X)` for some `X ∈ 𝓔` iff
`λ_*μ(· | occ(d))(w)/ν(w)` is constant on the state's support"); [[decision-problems-v2]] Q3
Kind: P
Fidelity: exact (multiplicative form; `P`-clause)
Hyps: (a) `0 < μ(occ(d))` -/
theorem occState_P_eq_nuCondDistr_iff (h : 0 < mass C B (occ d B)) :
    (∃ (X : Finset Ω) (hX : 0 < nu C B X), (occState C B d h).P = nuCondDistr C B X hX) ↔
      ∀ ω ω', 0 < mass C B (occEv B d {ω}) → 0 < mass C B (occEv B d {ω'}) →
        mass C B (occEv B d {ω}) * nu C B {ω'} = mass C B (occEv B d {ω'}) * nu C B {ω} := by
  have hw : ∀ ω, (occState C B d h).P.w ω = mass C B (occEv B d {ω}) / mass C B (occ d B) :=
    fun _ => rfl
  constructor
  · rintro ⟨X, hX, hP⟩ ω ω' hω hω'
    have key : ∀ ω, 0 < mass C B (occEv B d {ω}) →
        mass C B (occEv B d {ω}) * nu C B X = nu C B {ω} * mass C B (occ d B) := by
      intro ω hω
      have := congrArg (fun P : FinDistr K Ω => P.w ω) hP
      simp only [hw, nuCondDistr] at this
      split_ifs at this with hmem
      · rw [div_eq_div_iff h.ne' hX.ne'] at this
        exact this
      · exact absurd (div_pos hω h) (by rw [this]; exact lt_irrefl 0)
    have a := key ω hω
    have b := key ω' hω'
    apply mul_right_cancel₀ hX.ne'
    linear_combination nu C B {ω'} * a - nu C B {ω} * b
  · intro hconst
    obtain ⟨ω₀, hω₀⟩ : ∃ ω, 0 < mass C B (occEv B d {ω}) := by
      by_contra hc
      push_neg at hc
      have : mass C B (occ d B) = 0 := by
        rw [mass_occ_eq_sum_support]
        apply Finset.sum_eq_zero
        intro ω _
        exact le_antisymm (hc ω) (mass_nonneg C B _)
      exact h.ne' this
    have hS : 0 < nu C B (perRunSupport C B d) := by
      rw [nu_eq_sum_singleton]
      refine lt_of_lt_of_le (lt_of_lt_of_le hω₀ (mass_occEv_singleton_le_nu C B d ω₀)) ?_
      apply Finset.single_le_sum (fun ω _ => nu_nonneg C B {ω})
      simp [perRunSupport, hω₀]
    refine ⟨perRunSupport C B d, hS, ?_⟩
    apply FinDistr.ext'
    intro ω
    rw [hw]
    show _ = if ω ∈ perRunSupport C B d then nu C B {ω} / nu C B (perRunSupport C B d) else 0
    by_cases hmem : ω ∈ perRunSupport C B d
    · rw [if_pos hmem]
      have hω : 0 < mass C B (occEv B d {ω}) := by
        simpa [perRunSupport] using hmem
      rw [div_eq_div_iff h.ne' hS.ne', nu_eq_sum_singleton, mass_occ_eq_sum_support,
        Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω' hω' => ?_
      have hω'' : 0 < mass C B (occEv B d {ω'}) := by
        simpa [perRunSupport] using hω'
      have := hconst ω ω' hω hω''
      linear_combination this
    · rw [if_neg hmem]
      have : mass C B (occEv B d {ω}) = 0 := by
        simp only [perRunSupport, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hmem
        exact le_antisymm hmem (mass_nonneg C B _)
      rw [this, zero_div]

end expressible

end Cleanroom.Decision.DpFirstpersonSc
