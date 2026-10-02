import Cleanroom.Found.DpCoreTree

/-!
# dp-core-tree — audit round 3, adversarial lens: probes

Not imported by the library. Elaborated with `scripts/lean-check`.

1. **Disjointness is load-bearing in the repaired identity.** `recordsFor_iff_actRecordingOn`
   carries Definition 3's pairwise disjointness of action events as a hypothesis. With the action
   events all `⊤` (`allEv`, not disjoint) the coin-then-query tree is `ActRecordingOn` for every
   procedure (`allEv_actRecordingOn`) and meets `d` once on every run (`coinQuery_count`), yet it
   is **not** Definition-7 recorded (`allEv_not_recordsFor`: clause 4 fails — the leaf-world
   satisfies the other action's event too). So the (⇐) direction is false without `hdisj`; the
   theorem is not a syntactic restatement of `RecordsFor`, and its content is where the docstring
   says it is (node-action-veridicality + disjointness ⟹ clause 4).
2. **`ActRecordingOn` proved directly where clause (i) is a real constraint.** The package's
   direct witness `coinQuery_actRecordingOn` has `O_d = ⊤`, where clause (i)'s conclusion
   (subtree-veridicality) is automatic. On the routed coin-then-query tree `O_d = {o = 1}`, and
   `routedCoinQuery_actRecordingOn_direct` discharges clause (i) by inspecting the leaves below
   each active `d`-node; `routedCoinQuery_recordsFor_via_iff` then applies the (⇐) direction
   (with `rcqActEv_disjoint`) to recover `routedCoinQuery_recordsFor` a second way.
3. **The vacuity boundary of the screening headlines.** With `O_d = ∅`, `RecordsFor` and
   `PreQuery` are vacuously true for every tree and procedure and Lemma 3′'s four masses are all
   `0` (`recordsFor_of_obs_empty`, `preQuery_of_obs_empty`, `nu_empty`). `H*` is **not** vacuous
   there: its second clause forces `μ(occ(d)) = 0` (`hStar_obs_empty_iff_occ_null`). Every shipped
   witness realises `ν(O_d) ∈ {½, 1}` and `μ(occ(d)) ∈ {½, 1}`, so none sits on this boundary.
4. **SE-2's `|A_d| ≥ 2` clause (caveat c3).** A single-action point met twice on the only path
   is not `Nested` (`singleAction_not_nested`), and the two semantics agree on that tree for every
   procedure, as the iff's (⇐) direction requires (`singleAction_agree`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree.AuditR3

open Finset Tree Catalogue

/-! ### 1. Disjointness is load-bearing in `recordsFor_iff_actRecordingOn` -/

/-- Action events all `⊤`: every world satisfies every action — not pairwise disjoint. -/
def allEv (_ : Unit) (_ : Act2) : Finset CoinQueryW := Finset.univ

/-- With non-disjoint action events the coin-then-query tree is still `ActRecordingOn` for
every procedure: every `d`-node is trivially node-action-veridical and (with `O_d = ⊤`)
subtree-veridical, and every run passes exactly one `d`-node. -/
theorem allEv_actRecordingOn (C : Proc Unit (fun _ => Act2) ℚ) :
    ActRecordingOn cqObs allEv C coinQuery () := by
  refine ⟨fun _ _ _ _ _ _ => by simp [cqObs], ?_⟩
  intro ℓ _ _
  unfold coinQuery at ℓ ⊢
  rcases ℓ with ⟨i, act, _⟩
  refine ⟨⟨i, none⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_dNodesOn]
    simp [edgeOf_chance, edgeOf_decision_none]
  · intro _ _ _ _; simp [allEv]
  · rintro ⟨j, (_ | ⟨y, q'⟩)⟩ ⟨hq, _⟩
    · rw [mem_dNodesOn] at hq
      by_cases hji : j = i
      · subst hji; rfl
      · simp [edgeOf_chance, Ne.symm hji] at hq
    · exact q'.elim

/-- …but it is not Definition-7 recorded: on the positive run `(c = 1, a)` the leaf-world lies
in `allEv b` as well, so clause 4 ("only for the action drawn there") fails. Hence the (⇐)
direction of `recordsFor_iff_actRecordingOn` needs its disjointness hypothesis. -/
theorem allEv_not_recordsFor :
    ¬ RecordsFor cqObs allEv (procQ (1/2) (by norm_num) (by norm_num)) coinQuery () := by
  intro h
  have hpos : 0 < leafLaw (procQ (1/2) (by norm_num) (by norm_num)) coinQuery ⟨0, .a, ()⟩ := by
    unfold coinQuery
    simp [procQ, FinDistr.fair, FinDistr.coin, FinDistr.act2]
  have hobs : world coinQuery ⟨0, .a, ()⟩ ∈ cqObs () := by simp [cqObs]
  obtain ⟨-, h2⟩ := h _ hpos hobs
  have hedge : edgeOf coinQuery ⟨0, none⟩ ⟨0, .a, ()⟩ = some .a := by
    unfold coinQuery; simp [edgeOf_chance, edgeOf_decision_none]
  have := (h2 ⟨0, none⟩ rfl .a hedge).2.2 .b (by simp [allEv])
  cases this

/-! ### 2. A direct `ActRecordingOn` witness with an informative `O_d` -/

/-- The routed tree's action events at `d` are pairwise disjoint (Definition 3). -/
theorem rcqActEv_disjoint :
    ∀ x x' : Act2, x ≠ x' → Disjoint (rcqActEv .d x) (rcqActEv .d x') := by
  intro x x' h
  rw [Finset.disjoint_left]
  intro w hw hw'
  simp only [rcqActEv, Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
  exact h (hw.symm.trans hw')

/-- **`ActRecordingOn` on the routed coin-then-query tree, directly from the definition**, for
every procedure. Clause (i) is not automatic here (`O_d = {o = 1}`): each active `d`-node is
subtree-veridical because every leaf below it carries `o = 1`, and the `e = b` leaf (with
`o = 0`) lies below no `d`-node. -/
theorem routedCoinQuery_actRecordingOn_direct (C : Proc GatePt (fun _ => Act2) ℚ) :
    ActRecordingOn rcqObs rcqActEv C routedCoinQuery .d := by
  unfold routedCoinQuery
  refine ⟨?_, ?_⟩
  · -- clause (i): an active `d`-node is subtree-veridical
    rintro (_ | ⟨_ | _, q⟩) hq _ _
    · simp at hq
    · rcases q with ⟨i, (_ | ⟨y, q'⟩)⟩
      · rintro ⟨_ | _, ℓ'⟩ hℓ'
        · rcases ℓ' with ⟨j, act', _⟩; simp [rcqObs]
        · simp [edgeOf_decision_some] at hℓ'
      · exact q'.elim
    · exact q.elim
  · -- clause (ii): every positive `O_d`-run passes exactly one a.s.-node-action-veridical node
    intro ℓ _ hobs
    rcases ℓ with ⟨_ | _, ℓ⟩
    · rcases ℓ with ⟨i, act, _⟩
      refine ⟨some ⟨.a, ⟨i, none⟩⟩, ⟨?_, ?_⟩, ?_⟩
      · rw [mem_dNodesOn]
        simp [edgeOf_decision_some, edgeOf_chance, edgeOf_decision_none]
      · rintro ⟨_ | _, ℓ'⟩ x _ hx
        · rcases ℓ' with ⟨j, act', _⟩
          by_cases hji : j = i
          · subst hji
            simp only [edgeOf_decision_some, edgeOf_chance, dite_true, edgeOf_decision_none,
              Option.some.injEq] at hx
            subst hx
            simp [rcqActEv]
          · simp [edgeOf_decision_some, edgeOf_chance, hji] at hx
        · simp [edgeOf_decision_some] at hx
      · rintro (_ | ⟨_ | _, q⟩) ⟨hq, _⟩
        · rw [mem_dNodesOn] at hq; simp at hq
        · rcases q with ⟨j, (_ | ⟨y, q'⟩)⟩
          · rw [mem_dNodesOn] at hq
            by_cases hji : j = i
            · subst hji; rfl
            · simp [edgeOf_decision_some, edgeOf_chance, Ne.symm hji] at hq
          · exact q'.elim
        · exact q.elim
    · exfalso
      simp [rcqObs] at hobs

/-- Every `O_d`-run of the routed tree meets `d` exactly once. -/
theorem routedCoinQuery_count_one (ℓ : routedCoinQuery.Leaves)
    (hobs : world routedCoinQuery ℓ ∈ rcqObs .d) : count .d routedCoinQuery ℓ = 1 := by
  unfold routedCoinQuery at ℓ hobs ⊢
  rcases ℓ with ⟨_ | _, ℓ⟩
  · rcases ℓ with ⟨i, act, _⟩; simp
  · simp [rcqObs] at hobs

/-- **The repaired identity's (⇐) direction applied on a tree with an informative `O_d`**:
recording at `d` on the routed tree, recovered from the direct `ActRecordingOn` witness,
`#_d = 1` on the `O_d`-runs, and disjointness — a second proof of
`routedCoinQuery_recordsFor`. -/
theorem routedCoinQuery_recordsFor_via_iff (C : Proc GatePt (fun _ => Act2) ℚ) :
    RecordsFor rcqObs rcqActEv C routedCoinQuery .d :=
  (recordsFor_iff_actRecordingOn rcqObs rcqActEv C routedCoinQuery .d rcqActEv_disjoint).mpr
    ⟨routedCoinQuery_actRecordingOn_direct C, fun ℓ _ hobs => routedCoinQuery_count_one ℓ hobs⟩

/-! ### 3. The vacuity boundary: `O_d = ∅` -/

section boundary

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] [DecidableEq ι]
  [DecidableEq Ω]

/-- With `O_d = ∅`, recording is vacuous for every tree and procedure. -/
theorem recordsFor_of_obs_empty (actEv : (d : ι) → acts d → Finset Ω) (C : Proc ι acts K)
    (B : Tree Ω ι acts K) (d : ι) : RecordsFor (fun _ => ∅) actEv C B d :=
  fun _ _ h => absurd h (Finset.notMem_empty _)

/-- With `O_d = ∅`, every event is pre-query, vacuously. -/
theorem preQuery_of_obs_empty (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)
    (X : Finset Ω) : PreQuery (fun _ => ∅) C B d X :=
  fun _ _ h => absurd h (Finset.notMem_empty _)

/-- `ν(∅) = 0`, so with `O_d = ∅` all four masses of Lemma 3′ vanish and its conclusion is
`0 = 0`. -/
theorem nu_empty (C : Proc ι acts K) (B : Tree Ω ι acts K) : nu C B ∅ = 0 := by
  unfold nu mass worldEv
  simp

/-- `H*` with `O_d = ∅` is not vacuous: it holds iff no positive run meets a `d`-node, i.e.
`μ(occ(d)) = 0`. -/
theorem hStar_obs_empty_iff_occ_null (actEv : (d : ι) → acts d → Finset Ω)
    (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) :
    HStar (fun _ => ∅) actEv C B d ↔ mass C B (occ d B) = 0 := by
  constructor
  · rintro ⟨-, h⟩
    unfold mass
    apply Finset.sum_eq_zero
    intro ℓ hℓ
    rw [mem_occ] at hℓ
    rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hzero
    · exact absurd (h ℓ hpos hℓ) (Finset.notMem_empty _)
    · exact hzero.symm
  · intro h
    refine ⟨recordsFor_of_obs_empty actEv C B d, fun ℓ hpos hc => ?_⟩
    exfalso
    have hmem : ℓ ∈ occ d B := by rw [mem_occ]; exact hc
    have : leafLaw C B ℓ = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun ℓ' _ => leafLaw_nonneg C B ℓ')).mp h ℓ hmem
    rw [this] at hpos
    exact lt_irrefl 0 hpos

end boundary

/-! ### 4. SE-2's `|A_d| ≥ 2` clause -/

/-- A single-action point met twice on the only path. -/
def singleAction : Tree Unit Unit (fun _ => Unit) ℚ :=
  .decision () fun _ => .decision () fun _ => .leaf () 0

/-- Not nested: the point has one action (caveat c3). -/
theorem singleAction_not_nested : ¬ Nested singleAction () := by
  rintro ⟨h, -⟩
  rw [Fintype.card_unit] at h
  omega

/-- …so the two semantics agree on it for every procedure, as SE-2 (⇐) says. -/
theorem singleAction_agree (C : Proc Unit (fun _ => Unit) ℚ) (ℓ : singleAction.Leaves) :
    leafLaw C singleAction ℓ = leafLaw' C singleAction ℓ :=
  (agreement_iff_not_nested singleAction).mpr (fun ⟨_, h⟩ => singleAction_not_nested h) C ℓ

end Cleanroom.Found.DpCoreTree.AuditR3
