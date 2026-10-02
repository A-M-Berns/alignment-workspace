import Cleanroom.Found.DpCoreTree.ScreeningWitness
import Cleanroom.Found.DpCoreTree.RecordingFull
import Cleanroom.Found.DpCoreTree.RootEvents
import Cleanroom.Found.DpCoreTree.Faithful

/-!
# Witnesses added in repair round 1

Non-vacuity witnesses the round-1 audits asked for (adopted from the auditors' probes
`audit-r1-probes/Fidelity.lean` and `audit-r1-probes/Vacuity.lean` where they supplied one),
all on catalogue trees and computed from `leafLaw`:

* **`H*`** (`screening_ssc_of_hStar`'s hypothesis) is inhabited, for every procedure, by the
  coin-then-query tree (`coinQuery_hStar`) — degenerately for `H*`'s second clause, since
  `O_d = ⊤` there (adversarial audit r2 B1); the non-degenerate witness is
  `routedCoinQuery_hStar` in `WitnessesR2.lean`.
* **`ActRecordingOn`** (the repaired dp-cf-2-001 identity) is inhabited by the coin-then-query
  tree for every procedure, proved directly from the definition (`coinQuery_actRecordingOn`,
  repair round 2), with the iff's (⇐) direction then applied to recover recording
  (`coinQuery_recordsFor_of_actRecordingOn`, using `cqActEv_disjoint`); `B₁` at `C(d) = ½`
  through the iff's (⇒) direction (`mugActEv_disjoint`, `mug1_actRecordingOn`).
* **Root events** (T9): `{c = 1}` on the coin-then-query tree and `O_T` on `B₁` are root events
  with `ν = ½` for every procedure — neither `∅` nor `⊤` (`coinQuery_rootEvent`,
  `coinQuery_rootEvent_nu`, `mug1_rootEvent_obs`, `mug1_nu_obs_const`), and the headline
  instantiated (`coinQuery_rootEvent_invariant`, `rootEvent_nu_eq_instance`).
* **Run-level screening** (`screening_draw`, the repair of round 1's vacuous
  `screening_at_node`): on the coin-then-query tree with `X = {c = 1}`, `μ(X ∩ drew_a) = q/2`,
  `μ(occ) = 1`, `μ(X ∩ occ) = ½`, `μ(drew_a) = q` (`coinQuery_draw_values`,
  `coinQuery_screening_draw`).
* **The disposition identity** (T11, `disposition_faithful`) computed on `B₁` with `S` the
  `T`-runs and `a = pay`: `μ(S ∩ drew_pay) = q/2`, `μ_{C[d↦pay]}(occ) = 1`,
  `μ_{C[d↦pay]}(S ∩ occ) = ½`, `μ(drew_pay) = q`, so the identity reads `q/2 · 1 = ½ · q`
  (`mug1_disposition_values`, `mug1_disposition_instance`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree

open Finset Catalogue Tree

/-! ### `H*` and `ActRecordingOn` on the coin-then-query tree and `B₁` -/

/-- `H*` at `d` on the coin-then-query tree, for every procedure: recorded and `O_d = ⊤`, so
every run through a `d`-node is an `O_d`-run. **Degenerate for `H*`'s second clause**: with
`O_d = ⊤` that clause is automatic and `H*` is `RecordsFor` and nothing more
(`coinQuery_hStar_iff`, `WitnessesR2.lean`), so this instance exercises Lemma 3′'s aggregation
over two `d`-nodes but not the passage from the `O_d`-runs to `occ(d)`. The non-degenerate
`H*` witness is `routedCoinQuery_hStar` (`WitnessesR2.lean`).
Source: `sl-synthesis.md` line 20 (`H*`); fidelity audit r1 §3.1; adversarial audit r2 B1
Kind: N− (for `H*`'s second clause; N+ for the recording clause) -/
theorem coinQuery_hStar (C : Proc Unit (fun _ => Act2) ℚ) :
    HStar cqObs cqActEv C coinQuery () :=
  ⟨coinQuery_recordsFor C, fun _ _ _ => by simp [cqObs]⟩

/-- The coin-then-query tree's action events are pairwise disjoint (Definition 3).
Source: [[decision-problems-v2]] Definition 3
Kind: L -/
theorem cqActEv_disjoint : ∀ a a' : Act2, a ≠ a' → Disjoint (cqActEv () a) (cqActEv () a') := by
  intro a a' h
  rw [Finset.disjoint_left]
  intro w hw hw'
  simp [cqActEv] at hw hw'
  exact h (hw.symm.trans hw')

/-- The coin-then-query tree is `ActRecordingOn` at `d` for every procedure — proved **directly
from the definition** (every `d`-node is subtree-veridical since `O_d = ⊤`; the unique `d`-node
on a run's path is a.s. node-action-veridical because the leaves record the act), not through
`recordsFor_iff_actRecordingOn`, so that the iff's (⇐) direction can be seen doing work in
`coinQuery_recordsFor_of_actRecordingOn`.
Source: dp-cf-2-001 (repaired); fidelity audit r1 §3.3; adversarial audit r2 §3.4
Kind: N+ -/
theorem coinQuery_actRecordingOn (C : Proc Unit (fun _ => Act2) ℚ) :
    ActRecordingOn cqObs cqActEv C coinQuery () := by
  refine ⟨fun _ _ _ _ _ _ => by simp [cqObs], ?_⟩
  intro ℓ _ _
  unfold coinQuery at ℓ ⊢
  rcases ℓ with ⟨i, act, _⟩
  refine ⟨⟨i, none⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_dNodesOn]
    simp [edgeOf_chance, edgeOf_decision_none]
  · rintro ⟨j, act', _⟩ x _ hx
    by_cases hji : j = i
    · subst hji
      simp only [edgeOf_chance, dite_true, edgeOf_decision_none, Option.some.injEq] at hx
      subst hx
      simp [cqActEv]
    · simp [edgeOf_chance, hji] at hx
  · rintro ⟨j, (_ | ⟨y, q'⟩)⟩ ⟨hq, _⟩
    · rw [mem_dNodesOn] at hq
      by_cases hji : j = i
      · subst hji; rfl
      · simp [edgeOf_chance, Ne.symm hji] at hq
    · exact q'.elim

/-- **The repaired identity's (⇐) direction applied**: recording at `d` on the coin-then-query
tree recovered from the direct `ActRecordingOn` witness and `#_d = 1` — a second, independent
proof of `coinQuery_recordsFor`, through the direction that carries the content of
`recordsFor_iff_actRecordingOn`.
Source: dp-cf-2-001 (repaired); adversarial audit r2 §3.4
Kind: N+ -/
theorem coinQuery_recordsFor_of_actRecordingOn (C : Proc Unit (fun _ => Act2) ℚ) :
    RecordsFor cqObs cqActEv C coinQuery () :=
  (recordsFor_iff_actRecordingOn cqObs cqActEv C coinQuery () cqActEv_disjoint).mpr
    ⟨coinQuery_actRecordingOn C, fun ℓ _ _ => coinQuery_count ℓ⟩

/-- The mugging's action events are pairwise disjoint (Definition 3).
Source: [[decision-problems-v2]] Definition 3
Kind: L -/
theorem mugActEv_disjoint : ∀ a a' : Act2, a ≠ a' → Disjoint (mugActEv () a) (mugActEv () a') := by
  intro a a' h
  cases a <;> cases a' <;> simp_all [mugActEv]

/-- `B₁` at `C(d) = ½` is `ActRecordingOn` at `d` — obtained through the iff's (⇒) direction
from `mug1_recordsFor` (so this one inhabits the predicate but does not test the (⇐)
direction; `coinQuery_actRecordingOn` is the direct proof).
Source: dp-cf-2-001 (repaired); fidelity audit r1 §3.3
Kind: N+ -/
theorem mug1_actRecordingOn (x y : ℚ) :
    ActRecordingOn mugObs mugActEv (procQ (1/2) (by norm_num) (by norm_num)) (mug1 x y) () :=
  ((recordsFor_iff_actRecordingOn mugObs mugActEv _ (mug1 x y) () mugActEv_disjoint).mp
    (mug1_recordsFor x y)).1

/-! ### Root events (T9) -/

/-- `{c = 1}` is decided at every topmost decision node of the coin-then-query tree.
Source: `clean-source-and-policy-responsiveness.md` §3 (root events); fidelity audit r1 §3.2
Kind: N+ -/
theorem coinQuery_rootEvent : RootEvent coinQuery cqCoin := by
  intro q _
  unfold coinQuery at q ⊢
  rcases q with ⟨i', (_ | ⟨_b, q'⟩)⟩
  · by_cases hi : i' = 0
    · left
      rintro ⟨j, act, _⟩ hj
      rw [mem_leavesBelow] at hj
      by_cases hji : j = i'
      · subst hji; simp [cqCoin, hi]
      · simp [edgeOf_chance, hji] at hj
    · right
      rintro ⟨j, act, _⟩ hj
      rw [mem_leavesBelow] at hj
      by_cases hji : j = i'
      · subst hji; simp [cqCoin, hi]
      · simp [edgeOf_chance, hji] at hj
  · exact q'.elim

/-- `ν({c = 1}) = ½` for every procedure: T9's conclusion on an event that is neither `∅` nor
`⊤`.
Source: fidelity audit r1 §3.2
Kind: N+ -/
theorem coinQuery_rootEvent_nu (C : Proc Unit (fun _ => Act2) ℚ) :
    nu C coinQuery cqCoin = 1 / 2 := by
  rw [coinQuery_nu]
  have h := (C ()).sum_one
  rw [Act2.sum_univ] at h
  simp [Act2.sum_univ, cqCoin]
  linarith

/-- T9 applied to the coin-then-query witness.
Source: `clean-source-and-policy-responsiveness.md` §3; T9
Kind: N+ -/
theorem coinQuery_rootEvent_invariant (C C' : Proc Unit (fun _ => Act2) ℚ) :
    nu C coinQuery cqCoin = nu C' coinQuery cqCoin :=
  RootEvent.nu_eq cqCoin coinQuery coinQuery_rootEvent C C'

/-- `ν(O_T) = ½` on `B₁` for every procedure.
Source: adversarial audit r1 §3.4 (probe 3a)
Kind: N+ -/
theorem mug1_nu_obs_const (x y : ℚ) (C : Proc Unit (fun _ => Act2) ℚ) :
    nu C (mug1 x y) (mugObs ()) = 1 / 2 := by
  unfold nu worldEv
  rw [mug1_mass]
  have h := (C ()).sum_one
  rw [Act2.sum_univ] at h
  simp only [Fin.sum_univ_two, Act2.sum_univ, mug1, world_chance, world_decision, world_leaf,
    mugWorld1, mugObs]
  simp
  linarith

/-- `O_T` is a root event of `B₁` (decided at both topmost `d`-nodes).
Source: `clean-source-and-policy-responsiveness.md` §3; adversarial audit r1 §3.4 (probe 3b)
Kind: N+ -/
theorem mug1_rootEvent_obs (x y : ℚ) : RootEvent (mug1 x y) (mugObs ()) := by
  intro q _
  rcases q with ⟨i, _ | ⟨act, e⟩⟩
  · unfold DecidedAt
    fin_cases i
    · left
      intro ℓ hℓ
      rcases ℓ with ⟨j, ⟨act, _⟩⟩
      rw [mem_leavesBelow] at hℓ
      by_cases hj : j = 0
      · subst hj
        cases act <;> simp [mug1, mugWorld1, mugObs]
      · exfalso
        simp [mug1, edgeOf_chance, hj] at hℓ
    · right
      intro ℓ hℓ
      rcases ℓ with ⟨j, ⟨act, _⟩⟩
      rw [mem_leavesBelow] at hℓ
      by_cases hj : j = 1
      · subst hj
        cases act <;> simp [mug1, mugWorld1, mugObs]
      · exfalso
        simp [mug1, edgeOf_chance, hj] at hℓ
  · exact e.elim

/-- T9 applied to `B₁`: `ν(O_T)` is the same for every procedure (`= ½`, neither `0` nor `1`).
Source: T9; adversarial audit r1 §3.4 (probe 3c)
Kind: N+ -/
theorem rootEvent_nu_eq_instance (x y : ℚ) (C C' : Proc Unit (fun _ => Act2) ℚ) :
    nu C (mug1 x y) (mugObs ()) = nu C' (mug1 x y) (mugObs ()) :=
  RootEvent.nu_eq (mugObs ()) (mug1 x y) (mug1_rootEvent_obs x y) C C'

/-! ### Run-level screening on the coin-then-query tree -/

/-- `μ` on the coin-then-query tree of a run event as an explicit sum.
Source: none: infrastructure
Kind: L -/
theorem coinQuery_mass (C : Proc Unit (fun _ => Act2) ℚ) (P : coinQuery.Leaves → Prop)
    [DecidablePred P] :
    mass C coinQuery (Finset.univ.filter P) =
      ∑ i : Fin 2, ∑ act : Act2, if P ⟨i, ⟨act, ()⟩⟩ then (1/2 : ℚ) * (C ()).w act else 0 := by
  rw [mass_filter]
  unfold coinQuery
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  rw [Tree.sum_leaves_leaf]
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf, FinDistr.fair, FinDistr.coin,
    mul_one]
  fin_cases i <;> simp <;> norm_num

/-- The four run-level masses on the coin-then-query tree with `C(d) = (q, 1−q)` and
`X = {c = 1}`: `μ(X ∩ drew_a) = q/2`, `μ(occ) = 1`, `μ(X ∩ occ) = ½`, `μ(drew_a) = q`.
Source: mandate T6; `screening_draw`'s N+
Kind: N+ -/
theorem coinQuery_draw_values (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    mass (procQ q h0 h1) coinQuery (worldEv coinQuery cqCoin ∩ drew () .a coinQuery) = q / 2 ∧
    mass (procQ q h0 h1) coinQuery (occ () coinQuery) = 1 ∧
    mass (procQ q h0 h1) coinQuery (worldEv coinQuery cqCoin ∩ occ () coinQuery) = 1 / 2 ∧
    mass (procQ q h0 h1) coinQuery (drew () .a coinQuery) = q := by
  have hocc : occ () coinQuery = Finset.univ := by
    ext ℓ; simp [coinQuery_count]
  have e1 : worldEv coinQuery cqCoin ∩ drew () .a coinQuery =
      Finset.univ.filter fun ℓ => world coinQuery ℓ ∈ cqCoin ∧
        (⟨(), .a⟩ : Σ d : Unit, Act2) ∈ draws coinQuery ℓ := by
    ext ℓ; simp [worldEv]
  have e2 : worldEv coinQuery cqCoin ∩ occ () coinQuery =
      Finset.univ.filter fun ℓ => world coinQuery ℓ ∈ cqCoin := by
    rw [hocc, Finset.inter_univ]; rfl
  have e3 : drew () .a coinQuery =
      Finset.univ.filter fun ℓ => (⟨(), .a⟩ : Σ d : Unit, Act2) ∈ draws coinQuery ℓ := by
    ext ℓ; simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1, coinQuery_mass]
    simp [Act2.sum_univ, cqCoin, coinQuery, procQ, Sigma.mk.injEq, heq_eq_eq]
    ring
  · rw [hocc, mass_univ]
  · rw [e2, coinQuery_mass]
    simp [Act2.sum_univ, cqCoin, coinQuery, procQ]
    ring
  · rw [e3, coinQuery_mass]
    simp [coinQuery, procQ, Sigma.mk.injEq, heq_eq_eq]

/-- **Run-level screening instantiated**: on the coin-then-query tree, for every procedure and
`X = {c = 1}`, `μ(X ∩ drew_a) · μ(occ) = μ(X ∩ occ) · μ(drew_a)` (with `C(d) = (q, 1−q)`
this reads `q/2 · 1 = ½ · q`, `coinQuery_draw_values`).
Source: [[decision-problems-v2]] §7.3 Lemma 3, first clause; `screening_draw`
Kind: N+ -/
theorem coinQuery_screening_draw (C : Proc Unit (fun _ => Act2) ℚ) (a : Act2) :
    mass C coinQuery (worldEv coinQuery cqCoin ∩ drew () a coinQuery) *
        mass C coinQuery (occ () coinQuery) =
      mass C coinQuery (worldEv coinQuery cqCoin ∩ occ () coinQuery) *
        mass C coinQuery (drew () a coinQuery) :=
  screening_draw (fun ℓ _ => (coinQuery_count ℓ).le)
    (fun ℓ hpos q hq he => coinQuery_preQuery_coin C ℓ hpos (by simp [cqObs]) q hq he) a

/-! ### The disposition identity on `B₁` (T11) -/

/-- The four masses of the disposition identity on `B₁` with `C(d) = (q, 1−q)`, `S` the
`T`-runs and `a = pay`: `μ(S ∩ drew_pay) = q/2`, `μ_{C[d↦pay]}(occ) = 1`,
`μ_{C[d↦pay]}(S ∩ occ) = ½`, `μ(drew_pay) = q`.
Source: `faithful.md` FA-4; mandate T11; fidelity audit r1 §3.10
Kind: N+ -/
theorem mug1_disposition_values (x y q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    mass (procQ q h0 h1) (mug1 x y)
        (worldEv (mug1 x y) (mugObs ()) ∩ drew () .a (mug1 x y)) = q / 2 ∧
    mass ((procQ q h0 h1).deviatePure () .a) (mug1 x y) (occ () (mug1 x y)) = 1 ∧
    mass ((procQ q h0 h1).deviatePure () .a) (mug1 x y)
        (worldEv (mug1 x y) (mugObs ()) ∩ occ () (mug1 x y)) = 1 / 2 ∧
    mass (procQ q h0 h1) (mug1 x y) (drew () .a (mug1 x y)) = q := by
  have hocc : occ () (mug1 x y) = Finset.univ := by
    ext ℓ
    unfold mug1 at ℓ ⊢
    rcases ℓ with ⟨i, act, _⟩
    simp
  have e1 : worldEv (mug1 x y) (mugObs ()) ∩ drew () .a (mug1 x y) =
      Finset.univ.filter fun ℓ => world (mug1 x y) ℓ ∈ mugObs () ∧
        (⟨(), .a⟩ : Σ d : Unit, Act2) ∈ draws (mug1 x y) ℓ := by
    ext ℓ; simp [worldEv]
  have e2 : worldEv (mug1 x y) (mugObs ()) ∩ occ () (mug1 x y) =
      Finset.univ.filter fun ℓ => world (mug1 x y) ℓ ∈ mugObs () := by
    rw [hocc, Finset.inter_univ]; rfl
  have e3 : drew () .a (mug1 x y) =
      Finset.univ.filter fun ℓ => (⟨(), .a⟩ : Σ d : Unit, Act2) ∈ draws (mug1 x y) ℓ := by
    ext ℓ; simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1, mug1_mass]
    simp [Fin.sum_univ_two, Act2.sum_univ, mugObs, mugWorld1, mug1, procQ, Sigma.mk.injEq,
      heq_eq_eq]
    ring
  · rw [hocc, mass_univ]
  · rw [e2, mug1_mass]
    simp [Fin.sum_univ_two, Act2.sum_univ, mugObs, mugWorld1, mug1, Proc.deviatePure,
      Proc.deviate]
  · rw [e3, mug1_mass]
    simp [mug1, procQ, Sigma.mk.injEq, heq_eq_eq]

/-- **The disposition identity instantiated on `B₁`**: `disposition_faithful` at `S` = the
`T`-runs, `a = pay`, `C(d) = (q, 1−q)`; numerically `q/2 · 1 = ½ · q`
(`mug1_disposition_values`).
Source: `faithful.md` FA-4; mandate T11
Kind: N+ -/
theorem mug1_disposition_instance (x y q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    mass (procQ q h0 h1) (mug1 x y)
        (worldEv (mug1 x y) (mugObs ()) ∩ drew () .a (mug1 x y)) *
      mass ((procQ q h0 h1).deviatePure () .a) (mug1 x y) (occ () (mug1 x y)) =
    mass ((procQ q h0 h1).deviatePure () .a) (mug1 x y)
        (worldEv (mug1 x y) (mugObs ()) ∩ occ () (mug1 x y)) *
      mass (procQ q h0 h1) (mug1 x y) (drew () .a (mug1 x y)) :=
  disposition_faithful_of_almostFair (procQ q h0 h1) (mug1_almostFair x y) () .a _

end Cleanroom.Found.DpCoreTree
