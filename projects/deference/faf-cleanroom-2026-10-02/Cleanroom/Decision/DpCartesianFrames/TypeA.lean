import Cleanroom.Decision.DpCartesianFrames.Witnesses

/-!
# Type-(a) pseudo-observations: Transparent Newcomb at `Loc d_E` and `Loc d_F`, and Told-You-So

Package `dp-cartesian-frames`, file 18 (repair rounds 1 and 2; mandate T11(b), T9(c)). Lazy
seeding (CFF-5: no copies in TN-V1/V2, so lazy = identified). CF-20's type (a) is the failure
"membership is not even column-determined".

* **CF-16 / CFF-5, Transparent Newcomb V1 vs V2** (the catalogue's `tnV1`, `tnV2`). CF-16 makes
  two claims at two loci, and the package states both at their own locus:
  - **At `Loc d_E` (the V1/V2 wedge).** In V1 the partition `{S_E, S_F}` is a true Observation at
    `d_E`: `Loc d_E` is powerless outside the empty-box event `S_E` (`tnV1_loc_powerless_E`, CF-16
    line 91), hence `S_E` is observable (`tnV1_locE_observable_E`) and so is its complement, the
    full-box event `S_F` (`tnV1_locE_observable_F`; two-cell observability is symmetric). In V2 the
    hypothetical `d_E`-answer selects the chance node, so `S_E` is not column-determined, hence not
    observable, at `Loc d_E` (`tnV2_loc_not_columnDetermined_E`, `tnV2_locE_not_observable_E`,
    CF-16 line 92). The wedge is `tnV1_tnV2_wedge`.
  - **At `Loc d_F` (both variants).** The full-box event `S_F` is not column-determined, hence
    not a true Observation, at `d_F` in V1 and in V2 alike — the root simulation of `d_F` couples
    (`tnV1_locF_not_columnDetermined_F`, `tnV2_locF_not_columnDetermined_F` and the `¬ Observable2`
    corollaries; CF-16 line 94). Packaged as `tn_fullBox_not_observable_locF`.
  - What repair round 1 stated as "the full-box event is not [a true Observation]" was
    `tnV1_loc_not_powerless_F`: at `Loc d_E` of V1 the agent is *not powerless outside* `S_F` (it
    has power on the empty-box columns). That is a powerlessness asymmetry inside one observable
    partition, not a failure of observability (audit r2, both lenses); it is kept as what it is.
* **Told-You-So** (`toldYouSo`): chance-free, so `Fr` has one column; `O_5 = {n = 5}` is not
  column-determined and is controllable — the type-(a) witness for the truth test
  (`toldYouSo_not_columnDetermined_controllable`).
-/

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue

/-- A set is column-determined iff its complement is (membership and non-membership are
row-independent together).
Source: none: infrastructure (CF-8's notion is symmetric in the cells)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem columnDetermined_compl_iff {W : Type} (C : CartesianFrames.Frame W) (S : Set W) :
    ColumnDetermined C Sᶜ ↔ ColumnDetermined C S := by
  constructor
  · intro h e a₀ a₁
    have := h e a₀ a₁
    simp only [Set.mem_compl_iff] at this
    exact not_iff_not.mp this
  · intro h e a₀ a₁
    simp only [Set.mem_compl_iff]
    exact not_iff_not.mpr (h e a₀ a₁)

/-! ### Transparent Newcomb -/

section newcomb

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ)

/-- Membership in the Newcomb observations: `O_F = {fill = 1}`, `O_E = {fill = 0}`.
Source: none: infrastructure
Kind: L -/
theorem mem_tnObs_F (w : TnW) : w ∈ tnObs .F ↔ w.1 = true := by simp [tnObs]

theorem mem_tnObs_E (w : TnW) : w ∈ tnObs .E ↔ w.1 = false := by simp [tnObs]

/-- The full-box event is the complement of the empty-box event: `{S_E, S_F}` is one two-cell
partition of the worlds `TnW × ℚ`.
Source: cf-correspondence CF-16 (line 91: "`{S_E, S_F}`")
Kind: L -/
theorem SO_tnObs_F_eq_compl : (SO tnObs .F : Set (TnW × ℚ)) = (SO tnObs .E)ᶜ := by
  ext ⟨⟨f, act⟩, r⟩
  simp only [mem_SO, Set.mem_compl_iff, mem_tnObs_F, mem_tnObs_E]
  cases f <;> simp

/-- The `d_F`-coordinate of a `Loc d_E` column.
Source: none: infrastructure
Kind: D -/
def tnX (q : (e : {e : TnPt // e ≠ .E}) → Box) : Box := q ⟨.F, by decide⟩

/-- The run of `Loc d_E (tnV1)` at `(y, (q, ε))`: answer `x := q(d_F)` at the root, the coin of
`ε` at `x`, then the real branch.
Source: none: infrastructure
Kind: L -/
theorem tnV1_loc_outcome (y : Box) (q : (e : {e : TnPt // e ≠ .E}) → Box)
    (ε : ChanceProfile (tnV1 p h0 h1 L S)) :
    (Loc .E (tnV1 p h0 h1 L S)).outcome y (q, ε) =
      readout (tnV1 p h0 h1 L S) ⟨tnX q, ⟨(ε (tnX q)).1,
        runLeaf (extend .E y q) (tnReal L S (ε (tnX q)).1) ((ε (tnX q)).2 (ε (tnX q)).1)⟩⟩ := rfl

/-- The run of `Loc d_E (tnV2)` at `(y, (q, ε))`: answer `x := q(d_F)`, then `y`, the coin of
`ε` at `(x, y)`, then the real branch.
Source: none: infrastructure
Kind: L -/
theorem tnV2_loc_outcome (y : Box) (q : (e : {e : TnPt // e ≠ .E}) → Box)
    (ε : ChanceProfile (tnV2 p h0 h1 L S)) :
    (Loc .E (tnV2 p h0 h1 L S)).outcome y (q, ε) =
      readout (tnV2 p h0 h1 L S) ⟨tnX q, ⟨y, ⟨(ε (tnX q) y).1,
        runLeaf (extend .E y q) (tnReal L S (ε (tnX q) y).1)
          ((ε (tnX q) y).2 (ε (tnX q) y).1)⟩⟩⟩ := rfl

/-! #### At `Loc d_E`: V1 -/

/-- **CF-16, V1 at `d_E`: `Loc d_E (tnV1)` is powerless outside the empty-box event `S_E`** — on
a full-box column the world is `(1, x)` whatever `d_E` answers.
Source: cf-correspondence CF-16 (line 91: "Powerless outside `S_E`"); cf-frontier CFF-5
(line 68); mandate T11(b)
Kind: N+
Fidelity: exact (lazy; CFF-5: "No copies in TN-V1/V2, lazy = identified") -/
theorem tnV1_loc_powerless_E : PowerlessOutside (Loc .E (tnV1 p h0 h1 L S)) (SO tnObs .E) := by
  rintro ⟨q, ε⟩ y₀ y₁ hout
  rw [tnV1_loc_outcome] at hout ⊢
  rw [tnV1_loc_outcome]
  rcases hε : ε (tnX q) with ⟨i, f⟩
  rw [hε] at hout
  fin_cases i
  · rfl
  · exact absurd ((mem_SO _ _ _).mpr ((mem_tnObs_E _).mpr rfl)) hout

/-- **CF-16, V1 at `d_E`: the empty-box event is a true Observation** (observable in `Loc d_E`,
CF-20's definition), by CF-9 from powerlessness.
Source: cf-correspondence CF-16 (line 91: "hence `{S_E, S_F}` observable at `d_E` (CF-9)");
mandate T11(b)
Kind: N+
Fidelity: exact -/
theorem tnV1_locE_observable_E : Observable2 (Loc .E (tnV1 p h0 h1 L S)) (SO tnObs .E) :=
  (tnV1_loc_powerless_E p h0 h1 L S).observable2

/-- **CF-16, V1 at `d_E`: the full-box event is a true Observation too** — it is the other cell
of the same partition, and two-cell observability is symmetric in the cells. So at `Loc d_E` of
V1 the partition `{S_E, S_F}` is a true Observation; "cannot observe the full box" has no
rendering at this locus (its locus is `d_F`, below).
Source: cf-correspondence CF-16 (line 91: "`{S_E, S_F}` observable at `d_E`"); audit r2 (both
lenses, probes `TnV1FullObservable`/`TnFullBoxObservable`)
Kind: N+
Fidelity: exact -/
theorem tnV1_locE_observable_F : Observable2 (Loc .E (tnV1 p h0 h1 L S)) (SO tnObs .F) := by
  rw [SO_tnObs_F_eq_compl, observable2_compl_iff]
  exact tnV1_locE_observable_E p h0 h1 L S

/-- At `Loc d_E` of V1 the agent is **not powerless outside the full-box event**: on an
empty-box column the world is `(0, y)`, which depends on `d_E`'s answer. This is a powerlessness
asymmetry inside the observable partition `{S_E, S_F}` (post 11's one-sided notion: powerless
outside `S_E`, not outside `S_F`); it is **not** a failure of observability — `S_F` is observable
at `d_E` (`tnV1_locE_observable_F`). Repair round 1 glossed it as "the full-box event is not a
true Observation"; that gloss was false (audit r2).
Source: cf-correspondence CF-16 (line 91: "on `S_F`-outcomes the leaf is `(1, x)` — `y`-free",
the one-sided fact); none for the asymmetry itself
Kind: L
Fidelity: n/a (a side fact; CF-16's full-box clause is `tn_fullBox_not_observable_locF`) -/
theorem tnV1_loc_not_powerless_F :
    ¬ PowerlessOutside (Loc .E (tnV1 p h0 h1 L S)) (SO tnObs .F) := by
  intro h
  let q : (e : {e : TnPt // e ≠ .E}) → Box := fun _ => Box.large
  let ε : ChanceProfile (tnV1 p h0 h1 L S) := fun _ => (1, fun _ => Classical.arbitrary _)
  have h0' := h (q, ε) Box.large Box.both (by
    rw [tnV1_loc_outcome]
    intro hmem
    have hb : false = true := (mem_tnObs_F _).mp ((mem_SO _ _ _).mp hmem)
    exact Bool.noConfusion hb)
  rw [tnV1_loc_outcome, tnV1_loc_outcome] at h0'
  have h2 : ((false, Box.large), tnPay L S (false, Box.large)) =
      ((false, Box.both), tnPay L S (false, Box.both)) := h0'
  have h3 : Box.large = Box.both := congrArg (fun w => w.1.2) h2
  exact Box.noConfusion h3

/-! #### At `Loc d_E`: V2 -/

/-- **CF-16, V2 at `d_E`: the empty-box event is not even column-determined** — the hypothetical
`d_E`-answer selects the chance node, and a lazy column may show full under `large` and empty
under `both`.
Source: cf-correspondence CF-16 (line 92: "`x=1`, `ε₁₁=F`, `ε₁₂=E`: … Membership depends on
`y`: not column-determined"); cf-frontier CFF-5 (line 68: "`S_E` stays not column-determined");
mandate T11(b)
Kind: N+
Fidelity: exact -/
theorem tnV2_loc_not_columnDetermined_E :
    ¬ ColumnDetermined (Loc .E (tnV2 p h0 h1 L S)) (SO tnObs .E) := by
  intro h
  let q : (e : {e : TnPt // e ≠ .E}) → Box := fun _ => Box.large
  let ε : ChanceProfile (tnV2 p h0 h1 L S) :=
    fun _ y => (if y = Box.large then 0 else 1, fun _ => Classical.arbitrary _)
  have h0' := h (q, ε) Box.both Box.large
  rw [tnV2_loc_outcome, tnV2_loc_outcome] at h0'
  have hin : ((false, Box.both), tnPay L S (false, Box.both)) ∈ SO tnObs .E :=
    (mem_SO _ _ _).mpr ((mem_tnObs_E _).mpr rfl)
  have hout := h0'.mp hin
  have hb : true = false := (mem_tnObs_E _).mp ((mem_SO _ _ _).mp hout)
  exact Bool.noConfusion hb

/-- **CF-16, V2 at `d_E`: hence the empty-box event is not a true Observation** (CF-8).
Source: cf-correspondence CF-16 (line 92: "not column-determined, hence NOT observable (CF-8)")
Kind: C
Fidelity: exact -/
theorem tnV2_locE_not_observable_E :
    ¬ Observable2 (Loc .E (tnV2 p h0 h1 L S)) (SO tnObs .E) :=
  fun h => tnV2_loc_not_columnDetermined_E p h0 h1 L S h.columnDetermined

/-- The complement: nor is the full-box event column-determined at `Loc d_E` of V2 (a set is
column-determined iff its complement is).
Source: none: infrastructure
Kind: L -/
theorem tnV2_loc_not_columnDetermined_F :
    ¬ ColumnDetermined (Loc .E (tnV2 p h0 h1 L S)) (SO tnObs .F) := by
  rw [SO_tnObs_F_eq_compl, columnDetermined_compl_iff]
  exact tnV2_loc_not_columnDetermined_E p h0 h1 L S

/-- **CF-16 / CFF-5: the V1–V2 wedge is an observability difference at `Loc d_E`.** In V1 the
partition `{S_E, S_F}` is a true Observation at `d_E` (both cells observable); in V2 the
empty-box event is not column-determined, hence not observable, at `d_E`. Email 4's clause "the
agent observes the empty box" holds frame-side at `d_E` under the V1 tree and fails under V2;
its clause "cannot observe the full box" is a `d_F` fact true in both variants
(`tn_fullBox_not_observable_locF`), not part of the wedge. Which tree email 4 intends is
ATTRIBUTION-UNVETTED.
Source: cf-correspondence CF-16 (lines 84, 91–92: "the wedge IS an observability difference, at
the right locus … the V1/V2 difference lives entirely at `d_E`"); cf-frontier CFF-5 (line 68);
mandate T11(b)
Kind: N+
Fidelity: exact (the V2 half is stated for `S_E` as the source states it; its complement
`tnV2_loc_not_columnDetermined_F` is the same fact) -/
theorem tnV1_tnV2_wedge :
    (Observable2 (Loc .E (tnV1 p h0 h1 L S)) (SO tnObs .E) ∧
      Observable2 (Loc .E (tnV1 p h0 h1 L S)) (SO tnObs .F)) ∧
    (¬ ColumnDetermined (Loc .E (tnV2 p h0 h1 L S)) (SO tnObs .E) ∧
      ¬ Observable2 (Loc .E (tnV2 p h0 h1 L S)) (SO tnObs .E)) :=
  ⟨⟨tnV1_locE_observable_E p h0 h1 L S, tnV1_locE_observable_F p h0 h1 L S⟩,
    ⟨tnV2_loc_not_columnDetermined_E p h0 h1 L S, tnV2_locE_not_observable_E p h0 h1 L S⟩⟩

/-! #### At `Loc d_F`: the full-box event, both variants -/

/-- The run of `Loc d_F (tnV1)` at `(x, (q, ε))`: answer `x` at the root, the coin of `ε` at `x`,
then the real branch (where `d_E` answers `q(d_E)`).
Source: none: infrastructure
Kind: L -/
theorem tnV1_locF_outcome (x : Box) (q : (e : {e : TnPt // e ≠ .F}) → Box)
    (ε : ChanceProfile (tnV1 p h0 h1 L S)) :
    (Loc .F (tnV1 p h0 h1 L S)).outcome x (q, ε) =
      readout (tnV1 p h0 h1 L S) ⟨x, ⟨(ε x).1,
        runLeaf (extend .F x q) (tnReal L S (ε x).1) ((ε x).2 (ε x).1)⟩⟩ := rfl

/-- **CF-16 at `Loc d_F`, V1: the full-box event is not column-determined** (type (a)) — the
hypothetical `d_F`-answer selects the chance node, so a lazy column whose coin shows full under
`large` and empty under `both` sends the `large`-row to a fill-1 world and the `both`-row to a
fill-0 world.
Source: cf-correspondence CF-16 (line 94: "`O_F` fails at `Loc_{d_F}` in both variants (the root
sim of `d_F` couples in V1 and V2 alike)"); audit r2 (both lenses, probes
`FidTnFullBoxLocF`/`TnFullBoxLocF`)
Kind: N+
Fidelity: exact -/
theorem tnV1_locF_not_columnDetermined_F :
    ¬ ColumnDetermined (Loc .F (tnV1 p h0 h1 L S)) (SO tnObs .F) := by
  intro h
  let q : (e : {e : TnPt // e ≠ .F}) → Box := fun _ => Box.large
  let ε : ChanceProfile (tnV1 p h0 h1 L S) :=
    fun x => (if x = Box.large then 0 else 1, fun _ => Classical.arbitrary _)
  have h0' := h (q, ε) Box.large Box.both
  rw [tnV1_locF_outcome, tnV1_locF_outcome] at h0'
  have hin : ((true, Box.large), tnPay L S (true, Box.large)) ∈ SO tnObs .F :=
    (mem_SO _ _ _).mpr ((mem_tnObs_F _).mpr rfl)
  have hout := h0'.mp hin
  have hb : false = true := (mem_tnObs_F _).mp ((mem_SO _ _ _).mp hout)
  exact Bool.noConfusion hb

/-- **CF-16 at `Loc d_F`, V1: hence the full-box "observation" is not a true Observation** (CF-8).
Source: cf-correspondence CF-16 (line 94: "the full-box 'observation' is never a proper
Observation")
Kind: C
Fidelity: exact -/
theorem tnV1_locF_not_observable_F :
    ¬ Observable2 (Loc .F (tnV1 p h0 h1 L S)) (SO tnObs .F) :=
  fun h => tnV1_locF_not_columnDetermined_F p h0 h1 L S h.columnDetermined

/-- **CF-16 at `Loc d_F`, V2: the full-box event is not column-determined** — the same column
shape (coin full under `large`, empty under `both`, whatever `d_E` answers).
Source: cf-correspondence CF-16 (line 94); audit r2 (fidelity probe `FidTnFullBoxLocF`)
Kind: N+
Fidelity: exact -/
theorem tnV2_locF_not_columnDetermined_F :
    ¬ ColumnDetermined (Loc .F (tnV2 p h0 h1 L S)) (SO tnObs .F) := by
  intro h
  let q : (e : {e : TnPt // e ≠ .F}) → Box := fun _ => Box.large
  let ε : ChanceProfile (tnV2 p h0 h1 L S) :=
    fun x _ => (if x = Box.large then 0 else 1, fun _ => Classical.arbitrary _)
  have h0' := h (q, ε) Box.large Box.both
  have hin : (Loc .F (tnV2 p h0 h1 L S)).outcome Box.large (q, ε) ∈ SO tnObs .F := by
    show ((true, Box.large), tnPay L S (true, Box.large)) ∈ SO tnObs .F
    exact (mem_SO _ _ _).mpr ((mem_tnObs_F _).mpr rfl)
  have hout : (Loc .F (tnV2 p h0 h1 L S)).outcome Box.both (q, ε) ∉ SO tnObs .F := by
    show ((false, Box.large), tnPay L S (false, Box.large)) ∉ SO tnObs .F
    intro hm
    exact Bool.noConfusion ((mem_tnObs_F _).mp ((mem_SO _ _ _).mp hm))
  exact hout (h0'.mp hin)

/-- **CF-16 at `Loc d_F`, V2: hence not a true Observation** (CF-8).
Source: cf-correspondence CF-16 (line 94)
Kind: C
Fidelity: exact -/
theorem tnV2_locF_not_observable_F :
    ¬ Observable2 (Loc .F (tnV2 p h0 h1 L S)) (SO tnObs .F) :=
  fun h => tnV2_locF_not_columnDetermined_F p h0 h1 L S h.columnDetermined

/-- **CF-16's full-box clause: the full-box "observation" is never a proper Observation** — at
`Loc d_F` the event `S_F` is not column-determined, hence not observable, in V1 and in V2 alike.
This, not anything at `d_E`, is the frame-side rendering of email 4's "cannot observe the full
box" (ATTRIBUTION-UNVETTED); the V1/V2 difference lives entirely at `d_E` (`tnV1_tnV2_wedge`).
Source: cf-correspondence CF-16 (line 94: "`O_F` fails at `Loc_{d_F}` in both variants … the
full-box 'observation' is never a proper Observation, matching the email's sentence, while the
V1/V2 difference lives entirely at `d_E`"); mandate T11(b) ("the full-box event fails in both")
Kind: N+
Fidelity: exact -/
theorem tn_fullBox_not_observable_locF :
    (¬ ColumnDetermined (Loc .F (tnV1 p h0 h1 L S)) (SO tnObs .F) ∧
      ¬ Observable2 (Loc .F (tnV1 p h0 h1 L S)) (SO tnObs .F)) ∧
    (¬ ColumnDetermined (Loc .F (tnV2 p h0 h1 L S)) (SO tnObs .F) ∧
      ¬ Observable2 (Loc .F (tnV2 p h0 h1 L S)) (SO tnObs .F)) :=
  ⟨⟨tnV1_locF_not_columnDetermined_F p h0 h1 L S, tnV1_locF_not_observable_F p h0 h1 L S⟩,
    ⟨tnV2_locF_not_columnDetermined_F p h0 h1 L S, tnV2_locF_not_observable_F p h0 h1 L S⟩⟩

end newcomb

/-! ### Told-You-So: the type-(a) witness in the global frame -/

/-- Membership in `O_{d_k}`: the first coordinate is `k`.
Source: none: infrastructure
Kind: L -/
theorem mem_tysObs (k : Five10) (w : TysW) : w ∈ tysObs k ↔ w.1 = k := by simp [tysObs]

/-- **Told-You-So**: `O_5 = {n = 5}` is not column-determined in `Fr toldYouSo` (the tree is
chance-free — one column — and the row deciding `five` lands in `O_5`, the row deciding `ten`
outside) and it is controllable (ensurable by `five`, preventable by `ten`): CF-20's type (a),
the "observation" that is really a choice.
Source: cf-correspondence CF-20 (line 104: type (a)); CF-17 (line 96); mandate T9(c), T11(e)
("Told-You-So … chance-free with `O_5` `Controllable`")
Kind: N+
Fidelity: exact -/
theorem toldYouSo_not_columnDetermined_controllable :
    ¬ ColumnDetermined (Fr toldYouSo) (SO tysObs .five) ∧
    Controllable (Fr toldYouSo) (SO tysObs .five) := by
  refine ⟨fun h => ?_, ⟨fun _ => Five10.five, fun _ => ?_⟩, ⟨fun _ => Five10.ten, fun _ => ?_⟩⟩
  · have h1 := h (chanceProfileNonempty toldYouSo).some (fun _ => Five10.five) (fun _ => Five10.ten)
    have hin : (Fr toldYouSo).outcome (fun _ => Five10.five)
        (chanceProfileNonempty toldYouSo).some ∈ SO tysObs .five :=
      (mem_SO _ _ _).mpr ((mem_tysObs _ _).mpr rfl)
    have hout := h1.mp hin
    have hb : Five10.ten = Five10.five := (mem_tysObs _ _).mp ((mem_SO _ _ _).mp hout)
    exact Five10.noConfusion hb
  · exact (mem_SO _ _ _).mpr ((mem_tysObs _ _).mpr rfl)
  · intro hmem
    have hb : Five10.ten = Five10.five := (mem_tysObs _ _).mp ((mem_SO _ _ _).mp hmem)
    exact Five10.noConfusion hb

end Cleanroom.Decision.DpCartesianFrames
