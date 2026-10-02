import Cleanroom.Decision.DpCalibration.Basic
import Cleanroom.Found.DpCoreTree.Recording
import Cleanroom.Found.DpCoreTree.RecordingThms
import Mathlib.Logic.Equiv.Defs

/-!
# The veridicality bridge (Proposition 3), Remark 3.10, and the superconditioning lift
(Proposition 2)

T7, T8 and T20 of [[dp-calibration-mandate]].

* `mass_worldEv_inter_occ_eq_nu`, `mass_occ_eq_nu_obs`, `paySumLeaves_occ_eq_paySum` — under
  `H_d` (coverage and a.s. subtree-veridicality at every `d`-node, `dp-core-tree`'s
  `covers_and_veridical_iff`), the run-space events `{λ⊨X} ∩ occ(d)` and the world events
  `X ∧ O_d` carry the same mass and the same payoff mass.
* `perRunClausesAt_iff_strictClausesAt` / `perRunSSCAt_iff_strictOCAt` / `perRunSSC_iff_strictOC`
  — **Proposition 3**: the per-run SSC equations at `d` and the strict OC clauses at `d` are one
  equation; package-level when `H_d` holds at every queried point.
* `perRunClause1_not_strictClause1_of_occ_diff` — the half of Remark 3.10's converse that is
  true: if `μ(occ(d) ∖ {λ⊨O_d}) > 0` then no state is both per-run (clause 1) and strict
  (clause 1) at `d`. The other half (`{λ⊨O_d} ∖ occ(d)` positive) is **refuted** in
  `Witnesses.lean` (`splitWorld2`, N+; `splitWorld` is the N− one-world version): the two
  conditionals can coincide although the events differ — see findings F7.
* `relabel`, `relabelLeaves`, `lift`, `liftLeaves` — the tree over worlds `= Leaves(B)`;
  `leafLaw_relabel`, `value_lift`, `nu_lift`, `paySum_lift` — the lift preserves the run law,
  the value, and turns `ν'` into `μ`.
* `liftState`, `strictOC_lift` — **Proposition 2**: `lift B` is strictly observation-calibrated
  for the lifted states at the lifted observations `occ(d)`; `pushdown`,
  `pushdown_liftState_agree_iff_perRun` — the pushdown identity *is* the per-run hypothesis.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-! ## Proposition 3: the veridicality bridge -/

section bridge

variable (obs : ι → Finset Ω) (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- Under coverage and a.s. subtree-veridicality at every `d`-node,
`μ({λ⊨X} ∩ occ(d)) = ν(X ∧ O_d)`.
Source: [[decision-problems-v2]] §3.1 Proposition 3 ("`occ(d) = {λ ⊨ O_d}` up to `μ`-null sets")
Kind: P
Fidelity: exact
Hyps: (a) `Covers obs C B d`, (a) `∀ q, pt q = d → SubtreeVeridicalAS obs C B q` -/
theorem mass_worldEv_inter_occ_eq_nu {d : ι} (hcov : Covers obs C B d)
    (hver : ∀ q, pt B q = d → SubtreeVeridicalAS obs C B q) (X : Finset Ω) :
    mass C B (worldEv B X ∩ occ d B) = nu C B (X ∩ obs d) := by
  have hae := (covers_and_veridical_iff obs C B d).mp ⟨hcov, hver⟩
  unfold nu
  apply mass_congr_ae
  intro ℓ hpos
  simp only [Finset.mem_inter, worldEv, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hae ℓ hpos]

/-- Under the same hypotheses `μ(occ(d)) = ν(O_d)`.
Source: [[decision-problems-v2]] §3.1 Proposition 3; `zoo.md` ZO-2 ("vacuity coincides,
`μ(occ(d)) = ν(O_d)`")
Kind: L -/
theorem mass_occ_eq_nu_obs {d : ι} (hcov : Covers obs C B d)
    (hver : ∀ q, pt B q = d → SubtreeVeridicalAS obs C B q) :
    mass C B (occ d B) = nu C B (obs d) := by
  have := mass_worldEv_inter_occ_eq_nu obs C B hcov hver Finset.univ
  rwa [worldEv_univ, Finset.univ_inter, Finset.univ_inter] at this

/-- Under the same hypotheses the payoff masses agree.
Source: [[decision-problems-v2]] §3.1 Proposition 3 ("the `V`-clauses condition on one event")
Kind: L -/
theorem paySumLeaves_occ_eq_paySum {d : ι} (hcov : Covers obs C B d)
    (hver : ∀ q, pt B q = d → SubtreeVeridicalAS obs C B q) (X : Finset Ω) :
    (∑ ℓ ∈ worldEv B X ∩ occ d B, leafLaw C B ℓ * payoff B ℓ) = paySum C B (X ∩ obs d) := by
  have hae := (covers_and_veridical_iff obs C B d).mp ⟨hcov, hver⟩
  unfold paySum
  apply paySumLeaves_congr_ae
  intro ℓ hpos
  simp only [Finset.mem_inter, worldEv, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hae ℓ hpos]

/-- **Proposition 3 at a point, clause form**: under `H_d`, the per-run SSC clauses at `d` and
the strict OC clauses at `d` are the same equations.
Source: [[decision-problems-v2]] §3.1 Proposition 3 ("the per-run SSC equation at `d` and
clause 1 of strict OC at `d` are the *same equation*")
Kind: C
Fidelity: exact (both clauses, under the `V`-clause reading of record)
Hyps: (a) `Covers obs C B d`, (a) a.s. subtree-veridicality at every `d`-node -/
theorem perRunClausesAt_iff_strictClausesAt (s : ι → State Ω K) {d : ι}
    (hcov : Covers obs C B d) (hver : ∀ q, pt B q = d → SubtreeVeridicalAS obs C B q) :
    PerRunClausesAt s C B d ↔ StrictClausesAt s obs C B d := by
  unfold PerRunClausesAt StrictClausesAt PerRunClause1At PerRunClause2At StrictClause1At
    StrictClause2At
  simp only [mass_worldEv_inter_occ_eq_nu obs C B hcov hver, mass_occ_eq_nu_obs obs C B hcov hver,
    paySumLeaves_occ_eq_paySum obs C B hcov hver]

/-- **Proposition 3 at a point**: under `H_d`, per-run SSC at `d` ⟺ strict OC at `d` (the
positivity guards coincide as well).
Source: [[decision-problems-v2]] §3.1 Proposition 3
Kind: C
Fidelity: exact
Hyps: (a) `Covers obs C B d`, (a) a.s. subtree-veridicality at every `d`-node -/
theorem perRunSSCAt_iff_strictOCAt (s : ι → State Ω K) {d : ι}
    (hcov : Covers obs C B d) (hver : ∀ q, pt B q = d → SubtreeVeridicalAS obs C B q) :
    PerRunSSCAt s C B d ↔ StrictOCAt s obs C B d := by
  unfold PerRunSSCAt StrictOCAt
  rw [mass_occ_eq_nu_obs obs C B hcov hver, perRunClausesAt_iff_strictClausesAt obs C B s hcov hver]

/-- **Proposition 3, package level**: if `H_d` holds at every queried point, `B` is per-run SSC
for `C` iff strictly observation-calibrated for `C`.
Source: [[decision-problems-v2]] §3.1 Proposition 3 ("If this holds at every queried point")
Kind: C
Fidelity: exact
Hyps: (a) `H_d` at every queried `d` -/
theorem perRunSSC_iff_strictOC (s : ι → State Ω K)
    (hH : ∀ d ∈ queried B, Covers obs C B d ∧ ∀ q, pt B q = d → SubtreeVeridicalAS obs C B q) :
    PerRunSSC s C B ↔ StrictOC s obs C B := by
  unfold PerRunSSC StrictOC
  constructor
  · intro h d hd
    exact (perRunSSCAt_iff_strictOCAt obs C B s (hH d hd).1 (hH d hd).2).mp (h d hd)
  · intro h d hd
    exact (perRunSSCAt_iff_strictOCAt obs C B s (hH d hd).1 (hH d hd).2).mpr (h d hd)

/-- **Remark 3.10, the true half of the converse**: if `μ(occ(d) ∖ {λ ⊨ O_d}) > 0` and
`ν(O_d) > 0`, no state satisfies both the per-run clause 1 and the strict clause 1 at `d`
(the two conditionals differ on `X := O_d`). The other half — `{λ ⊨ O_d} ∖ occ(d)` positive —
does **not** force a divergence: see `splitWorld2` (N+, two worlds) and `splitWorld` (N−) in
`Witnesses.lean` and findings F7.
Source: [[decision-problems-v2]] §3.1 Remark 3.10 ("the divergence … is exactly the symmetric
difference") — reading: divergence of the *calibrated states*; ATTRIBUTION-UNVETTED
Kind: P
Fidelity: weaker: one direction of the symmetric difference only (the other is refuted)
Hyps: (a) `0 < μ(occ(d) ∖ {λ⊨O_d})`, (a) `0 < ν(O_d)` -/
theorem perRunClause1_not_strictClause1_of_occ_diff (s : ι → State Ω K) {d : ι}
    (hdiff : 0 < mass C B (occ d B \ worldEv B (obs d))) (hpos : 0 < nu C B (obs d))
    (hrun : PerRunClause1At s C B d) : ¬ StrictClause1At s obs C B d := by
  intro hstrict
  have h1 : (s d).pr (obs d) = 1 := by
    have := hstrict (obs d)
    rw [Finset.inter_self] at this
    have h' : (s d).pr (obs d) * nu C B (obs d) = 1 * nu C B (obs d) := by rw [this, one_mul]
    exact mul_right_cancel₀ hpos.ne' h'
  have h2 := hrun (obs d)
  rw [h1, one_mul] at h2
  -- `μ(occ) = μ(occ ∩ wO) + μ(occ ∖ wO)`
  have hsplit : mass C B (occ d B) =
      mass C B (occ d B \ worldEv B (obs d)) + mass C B (occ d B ∩ worldEv B (obs d)) := by
    rw [← mass_union C B (Finset.disjoint_sdiff_inter _ _), Finset.sdiff_union_inter]
  rw [Finset.inter_comm] at h2
  linarith

end bridge

/-! ## Proposition 2: the superconditioning lift -/

section lift

/-- Re-world a tree along a function of its leaves: the leaf at address `ℓ` gets the world
`f ℓ`, everything else unchanged. `lift B := relabel B id` puts the leaf address itself as the
world.
Source: [[decision-problems-v2]] §3.1 Proposition 2 ("define `B'` with the same tree,
`λ' = id`, payoffs unchanged")
Kind: D -/
def relabel {W : Type} : (T : Tree Ω ι acts K) → (T.Leaves → W) → Tree W ι acts K
  | .leaf _ r, f => .leaf (f ()) r
  | .chance n β child, f => .chance n β fun i => relabel (child i) fun ℓ => f ⟨i, ℓ⟩
  | .decision d child, f => .decision d fun a => relabel (child a) fun ℓ => f ⟨a, ℓ⟩

/-- The leaves of the re-worlded tree are the leaves of the original (same shape).
Source: [[decision-problems-v2]] §3.1 Proposition 2 ("the same tree")
Kind: D -/
def relabelLeaves {W : Type} :
    (T : Tree Ω ι acts K) → (f : T.Leaves → W) → (relabel T f).Leaves ≃ T.Leaves
  | .leaf _ _, _ => Equiv.refl Unit
  | .chance _ _ child, f => Equiv.sigmaCongrRight fun i => relabelLeaves (child i) fun ℓ => f ⟨i, ℓ⟩
  | .decision _ child, f => Equiv.sigmaCongrRight fun a => relabelLeaves (child a) fun ℓ => f ⟨a, ℓ⟩

/-- The world at a re-worlded leaf is `f` of the corresponding original leaf.
Source: none: infrastructure. Kind: L -/
theorem world_relabel {W : Type} :
    (T : Tree Ω ι acts K) → (f : T.Leaves → W) → ∀ ℓ', world (relabel T f) ℓ' = f (relabelLeaves T f ℓ')
  | .leaf _ _, _, _ => rfl
  | .chance _ _ child, f, ⟨i, ℓ'⟩ => world_relabel (child i) (fun ℓ => f ⟨i, ℓ⟩) ℓ'
  | .decision _ child, f, ⟨a, ℓ'⟩ => world_relabel (child a) (fun ℓ => f ⟨a, ℓ⟩) ℓ'

/-- Payoffs are unchanged by re-worlding. Source: none: infrastructure. Kind: L -/
theorem payoff_relabel {W : Type} :
    (T : Tree Ω ι acts K) → (f : T.Leaves → W) → ∀ ℓ',
      payoff (relabel T f) ℓ' = payoff T (relabelLeaves T f ℓ')
  | .leaf _ _, _, _ => rfl
  | .chance _ _ child, f, ⟨i, ℓ'⟩ => payoff_relabel (child i) (fun ℓ => f ⟨i, ℓ⟩) ℓ'
  | .decision _ child, f, ⟨a, ℓ'⟩ => payoff_relabel (child a) (fun ℓ => f ⟨a, ℓ⟩) ℓ'

/-- **The re-worlded tree has the same run law** (the content of Proposition 2's "the run
distribution … [is] unchanged").
Source: [[decision-problems-v2]] §3.1 Proposition 2
Kind: P
Fidelity: exact
Hyps: none -/
theorem leafLaw_relabel {W : Type} (C : Proc ι acts K) :
    (T : Tree Ω ι acts K) → (f : T.Leaves → W) → ∀ ℓ',
      leafLaw C (relabel T f) ℓ' = leafLaw C T (relabelLeaves T f ℓ')
  | .leaf _ _, _, _ => rfl
  | .chance _ β child, f, ⟨i, ℓ'⟩ => by
      show β.w i * leafLaw C (relabel (child i) _) ℓ' = β.w i * leafLaw C (child i) _
      rw [leafLaw_relabel C (child i) (fun ℓ => f ⟨i, ℓ⟩) ℓ']
  | .decision d child, f, ⟨a, ℓ'⟩ => by
      show (C d).w a * leafLaw C (relabel (child a) _) ℓ' = (C d).w a * leafLaw C (child a) _
      rw [leafLaw_relabel C (child a) (fun ℓ => f ⟨a, ℓ⟩) ℓ']

/-- `#_d` is unchanged by re-worlding. Source: none: infrastructure. Kind: L -/
theorem count_relabel {W : Type} (d : ι) :
    (T : Tree Ω ι acts K) → (f : T.Leaves → W) → ∀ ℓ',
      count d (relabel T f) ℓ' = count d T (relabelLeaves T f ℓ')
  | .leaf _ _, _, _ => rfl
  | .chance _ _ child, f, ⟨i, ℓ'⟩ => count_relabel d (child i) (fun ℓ => f ⟨i, ℓ⟩) ℓ'
  | .decision d' child, f, ⟨a, ℓ'⟩ => by
      show (if d' = d then 1 else 0) + count d (relabel (child a) _) ℓ' =
        (if d' = d then 1 else 0) + count d (child a) _
      rw [count_relabel d (child a) (fun ℓ => f ⟨a, ℓ⟩) ℓ']

/-- Queried points are unchanged by re-worlding. Source: none: infrastructure. Kind: L -/
theorem queried_relabel {W : Type} :
    (T : Tree Ω ι acts K) → (f : T.Leaves → W) → queried (relabel T f) = queried T
  | .leaf _ _, _ => rfl
  | .chance _ _ child, f => by
      show (Finset.univ.biUnion fun i => queried (relabel (child i) _)) = _
      simp only [queried_relabel (child _) _]
      rfl
  | .decision _ child, f => by
      show insert _ (Finset.univ.biUnion fun a => queried (relabel (child a) _)) = _
      simp only [queried_relabel (child _) _]
      rfl

/-- **The lift `B'` of Proposition 2**: the same tree over worlds `Leaves(B)`, the leaf at
address `ℓ` carrying world `ℓ`.
Source: [[decision-problems-v2]] §3.1 Proposition 2 (`𝓔' := 2^{Leaves(B)}`, `λ' = id`)
Kind: D
Fidelity: exact -/
def lift (B : Tree Ω ι acts K) : Tree B.Leaves ι acts K := relabel B id

/-- `Leaves(B') ≃ Leaves(B)`. Source: [[decision-problems-v2]] Proposition 2. Kind: D -/
def liftLeaves (B : Tree Ω ι acts K) : (lift B).Leaves ≃ B.Leaves := relabelLeaves B id

/-- The world of a lifted leaf is the corresponding original leaf (`λ' = id`).
Source: [[decision-problems-v2]] Proposition 2. Kind: L -/
theorem world_lift (B : Tree Ω ι acts K) (ℓ' : (lift B).Leaves) :
    world (lift B) ℓ' = liftLeaves B ℓ' := world_relabel B id ℓ'

/-- Payoffs on the lift. Source: [[decision-problems-v2]] Proposition 2. Kind: L -/
theorem payoff_lift (B : Tree Ω ι acts K) (ℓ' : (lift B).Leaves) :
    payoff (lift B) ℓ' = payoff B (liftLeaves B ℓ') := payoff_relabel B id ℓ'

/-- The lift preserves the run law. Source: [[decision-problems-v2]] Proposition 2. Kind: L -/
theorem leafLaw_lift (C : Proc ι acts K) (B : Tree Ω ι acts K) (ℓ' : (lift B).Leaves) :
    leafLaw C (lift B) ℓ' = leafLaw C B (liftLeaves B ℓ') := leafLaw_relabel C B id ℓ'

/-- **The lift preserves the value**: `V_{B'}(C) = V_B(C)`.
Source: [[decision-problems-v2]] §3.1 Proposition 2 ("the run distribution and value are
unchanged")
Kind: P
Fidelity: exact
Hyps: none -/
theorem value_lift (C : Proc ι acts K) (B : Tree Ω ι acts K) : value C (lift B) = value C B := by
  unfold value
  exact Fintype.sum_equiv (liftLeaves B) _ _ fun ℓ' => by
    rw [leafLaw_lift, payoff_lift]

/-- **`ν'` on the lift is `μ` on `B`**: for `X' ⊆ Leaves(B)`, `ν_{B',C}(X') = μ_{B,C}(X')`.
Source: [[decision-problems-v2]] §3.1 Proposition 2 ("whose worlds are exactly the leaves")
Kind: P
Fidelity: exact
Hyps: none -/
theorem nu_lift (C : Proc ι acts K) (B : Tree Ω ι acts K) (X' : Finset B.Leaves) :
    nu C (lift B) X' = mass C B X' := by
  rw [nu_eq_sum]
  have h : mass C B X' = ∑ ℓ, if ℓ ∈ X' then leafLaw C B ℓ else 0 := by
    unfold mass; rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h]
  exact Fintype.sum_equiv (liftLeaves B) _ _ fun ℓ' => by
    rw [leafLaw_lift, world_lift]

/-- The payoff mass on the lift is the payoff mass of the leaf set on `B`.
Source: [[decision-problems-v2]] Proposition 2. Kind: L -/
theorem paySum_lift (C : Proc ι acts K) (B : Tree Ω ι acts K) (X' : Finset B.Leaves) :
    paySum C (lift B) X' = ∑ ℓ ∈ X', leafLaw C B ℓ * payoff B ℓ := by
  rw [paySum_eq_sum_ite]
  rw [show (∑ ℓ ∈ X', leafLaw C B ℓ * payoff B ℓ) =
      ∑ ℓ, if ℓ ∈ X' then leafLaw C B ℓ * payoff B ℓ else 0 by
    rw [Finset.sum_ite_mem, Finset.univ_inter]]
  exact Fintype.sum_equiv (liftLeaves B) _ _ fun ℓ' => by
    rw [leafLaw_lift, world_lift, payoff_lift]

/-- **The lifted states `s'_d`**: `P := μ(· | occ(d))`, `V := its conditional value` — the
`calibratedState` of the lift at the lifted observation `occ(d)` — where `μ(occ(d)) > 0`, and
the default state where `occ(d)` is null (that point is unconstrained by every sense).
Source: [[decision-problems-v2]] §3.1 Proposition 2 (`P_{s'_d} := μ(· | occ(d))`)
Kind: D
Fidelity: exact on the positive points; the null points carry a default -/
noncomputable def liftState [∀ d, Nonempty (acts d)] (C : Proc ι acts K) (B : Tree Ω ι acts K)
    (d : ι) : State B.Leaves K :=
  if h : 0 < mass C B (occ d B) then
    calibratedState C (lift B) (occ d B) (by rwa [nu_lift])
  else
    haveI : Nonempty B.Leaves := leaves_nonempty B
    State.trivial

/-- **Proposition 2 (the calibration clause)**: `lift B` is strictly observation-calibrated for
`C` with the lifted states at the lifted observations `occ(d)`. The lifted state is *defined* as
the conditional (`calibratedState`), so the content is `nu_lift`/`paySum_lift` (the lift turns
`ν'` into `μ`) plus `μ(occ(d)) > 0 ↔ ν'(occ(d)) > 0`; a ledger row calling this `P` would be a
squeeze — it is `C`. Caveat 2.1: the lifted states are new objects with credences over runs
(over which node of the tree they inhabit, hypothetical instances included); whether `B'` is
"the same problem" is v2's Question 3, not decided here.
Source: [[decision-problems-v2]] §3.1 Proposition 2 ("`B'` is strictly observation-calibrated
for `C'`, the lifted observation being `occ(d)` itself"); Caveat 2.1
Kind: C
Fidelity: exact (`C'` agreeing with `C` at lifted points is `C` itself: the points are the same
labels `ι`)
Hyps: none -/
theorem strictOC_lift [∀ d, Nonempty (acts d)] (C : Proc ι acts K) (B : Tree Ω ι acts K) :
    StrictOC (liftState C B) (fun d => occ d B) C (lift B) := by
  intro d _ hpos
  have hm : 0 < mass C B (occ d B) := by rwa [nu_lift] at hpos
  apply strictClausesAt_calibratedState (fun d => occ d B) C (lift B) (liftState C B) d hpos
  unfold liftState
  rw [dif_pos hm]

/-- `∑_{ω ∈ X} P({ℓ : λ(ℓ) = ω}) = P({ℓ : λ(ℓ) ⊨ X})`. Source: none: infrastructure. Kind: L -/
theorem sum_probOf_worldEv_singleton (B : Tree Ω ι acts K) (P : FinDistr K B.Leaves)
    (X : Finset Ω) : ∑ ω ∈ X, probOf P (worldEv B {ω}) = probOf P (worldEv B X) := by
  simp only [probOf, worldEv, Finset.sum_filter, Finset.mem_singleton]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  exact Finset.sum_ite_eq X (world B ℓ) (fun _ => P.w ℓ)

/-- The pushforward `λ_* P` of a distribution on runs along `λ = world B`.
Source: [[decision-problems-v2]] §3.1 Proposition 2 (`λ_* P_{s'_d}`)
Kind: D -/
def pushdownDistr (B : Tree Ω ι acts K) (P : FinDistr K B.Leaves) : FinDistr K Ω where
  w ω := probOf P (worldEv B {ω})
  nonneg _ := probOf_nonneg _ _
  sum_one := by rw [sum_probOf_worldEv_singleton, worldEv_univ, probOf_univ]

/-- `(λ_* P)(X) = P({λ ⊨ X})`. Source: none: infrastructure. Kind: L -/
theorem probOf_pushdownDistr (B : Tree Ω ι acts K) (P : FinDistr K B.Leaves) (X : Finset Ω) :
    probOf (pushdownDistr B P) X = probOf P (worldEv B X) :=
  sum_probOf_worldEv_singleton B P X

/-- **Pushdown of a state on runs to a state on worlds** along `λ = world B`:
`(λ_* P)(X) = P({ℓ : λ(ℓ) ⊨ X})`, `V(X) := V({ℓ : λ(ℓ) ⊨ X})`.
Source: [[decision-problems-v2]] §3.1 Proposition 2 (`λ_* P_{s'_d}`)
Kind: D -/
def pushdown (B : Tree Ω ι acts K) (t : State B.Leaves K) : State Ω K where
  P := pushdownDistr B t.P
  V X := t.V (worldEv B X)
  avg X Y hXY hX hY := by
    simp only [probOf_pushdownDistr] at hX hY ⊢
    have hU : worldEv B (X ∪ Y) = worldEv B X ∪ worldEv B Y := by
      ext ℓ; simp [worldEv, Finset.mem_union]
    have hdisj : Disjoint (worldEv B X) (worldEv B Y) := by
      rw [Finset.disjoint_left]
      intro ℓ h1 h2
      simp only [worldEv, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact Finset.disjoint_left.mp hXY h1 h2
    rw [hU]
    exact t.avg _ _ hdisj hX hY

/-- `(λ_* t)(X) = P_t({λ ⊨ X})`. Source: none: infrastructure. Kind: L -/
theorem pushdown_pr (B : Tree Ω ι acts K) (t : State B.Leaves K) (X : Finset Ω) :
    (pushdown B t).pr X = probOf t.P (worldEv B X) :=
  probOf_pushdownDistr B t.P X

/-- `V` of the pushdown. Source: none: infrastructure. Kind: L -/
theorem pushdown_V (B : Tree Ω ι acts K) (t : State B.Leaves K) (X : Finset Ω) :
    (pushdown B t).V X = t.V (worldEv B X) := rfl

/-- **The pushdown identity is the per-run hypothesis** (Proposition 2's "`λ_* P_{s'_d} = P_{s_d}`
— this equation *is* the per-run SSC hypothesis"): where `μ(occ(d)) > 0`, the pushdown of the
lifted state agrees with `s_d` (modulo junk `V`) iff the per-run SSC clauses hold for `s_d`.
Source: [[decision-problems-v2]] §3.1 Proposition 2
Kind: L
Fidelity: exact (agreement modulo `V`'s junk values, `State.Agree`)
Hyps: (a) `0 < μ(occ(d))` -/
theorem pushdown_liftState_agree_iff_perRun [∀ d, Nonempty (acts d)] (C : Proc ι acts K)
    (B : Tree Ω ι acts K) (s : ι → State Ω K) {d : ι} (hm : 0 < mass C B (occ d B)) :
    State.Agree (pushdown B (liftState C B d)) (s d) ↔ PerRunClausesAt s C B d := by
  have hn : 0 < nu C (lift B) (occ d B) := by rwa [nu_lift]
  have hls : liftState C B d = calibratedState C (lift B) (occ d B) hn := by
    unfold liftState; rw [dif_pos hm]
  have hpr : ∀ X, (pushdown B (liftState C B d)).pr X =
      mass C B (worldEv B X ∩ occ d B) / mass C B (occ d B) := by
    intro X
    rw [pushdown_pr, hls]
    have := calibratedState_pr C (lift B) (occ d B) hn (worldEv B X)
    simp only [State.pr] at this
    rw [this, nu_lift, nu_lift]
  have hV : ∀ X, (pushdown B (liftState C B d)).V X =
      (∑ ℓ ∈ worldEv B X ∩ occ d B, leafLaw C B ℓ * payoff B ℓ) /
        mass C B (worldEv B X ∩ occ d B) := by
    intro X
    rw [pushdown_V, hls, calibratedState_V, paySum_lift, nu_lift]
  constructor
  · rintro ⟨hP, hVa⟩
    refine ⟨fun X => ?_, fun X hX hXm => ?_⟩
    · have := hpr X
      simp only [State.pr] at this ⊢
      rw [← hP, this]
      exact div_mul_cancel₀ _ hm.ne'
    · have hX' : 0 < (pushdown B (liftState C B d)).pr X := by
        simp only [State.pr, hP]; exact hX
      rw [← hVa X hX', hV X]
      exact div_mul_cancel₀ _ hXm.ne'
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun X hX => ?_⟩
    · apply FinDistr.ext'
      intro ω
      have := h1 {ω}
      have hp := hpr {ω}
      simp only [State.pr, probOf_singleton] at this hp ⊢
      rw [hp, ← this]
      exact mul_div_cancel_right₀ _ hm.ne'
    · have hp := hpr X
      rw [hp] at hX
      have hXm : 0 < mass C B (worldEv B X ∩ occ d B) := by
        by_contra hc
        rw [not_lt] at hc
        have := div_nonpos_of_nonpos_of_nonneg hc (mass_nonneg C B (occ d B))
        linarith
      have hsX : 0 < (s d).pr X := by
        have := h1 X
        have : (s d).pr X = mass C B (worldEv B X ∩ occ d B) / mass C B (occ d B) := by
          rw [eq_div_iff hm.ne']; exact this
        rw [this]; exact div_pos hXm hm
      rw [hV X]
      have := h2 X hsX hXm
      rw [div_eq_iff hXm.ne']
      exact this.symm

/-- **Per-run SSC from prior calibration when `occ(d)` is every run**: if `occ d B = univ` then
a prior-calibrated state at `d` satisfies the per-run clauses (the clauses collapse to
Definition 11).
Source: [[decision-problems-v2]] §3.1 Definition 13 (with `occ(d) = Leaves`); Observation 1
Kind: L -/
theorem perRunClausesAt_of_priorCalibrated_of_occ_univ (C : Proc ι acts K) (B : Tree Ω ι acts K)
    (s : ι → State Ω K) {d : ι} (hocc : occ d B = Finset.univ)
    (hprior : PriorCalibrated C B (s d)) : PerRunClausesAt s C B d := by
  refine ⟨fun X => ?_, fun X _ hX => ?_⟩
  · rw [hocc, Finset.inter_univ, mass_univ, mul_one]
    exact hprior.1 X
  · rw [hocc, Finset.inter_univ] at hX ⊢
    exact hprior.2 X hX

end lift

end Cleanroom.Decision.DpCalibration
