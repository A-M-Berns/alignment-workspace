/-
# Forgetting: projection computed, what is safe to forget, loss as slack, and choice

Round `projects/normativity/rounds/2026-11-08-content-recollection/`, follow-up of 2026-11-09,
matter 3.

§1.  **Projection is computed.**  One Fourier–Motzkin step (`FourierMotzkin.elim`, the step
`SeedStatics.project` iterates) on a list of rows with coordinate `k` moved last (`eliminate`)
has as its rational solutions exactly the projection of the list's solutions along the
coordinate map `k.succAbove` that drops `k` (`eliminate_sat_iff`).  For a bundle, `forget k B`
is a bundle on the retained coordinates whose region is `Conservativity.projection` of `B`'s
(`forget_region`).  **Forgetting is exact on the retained fragment**: a row over the retained
coordinates is forced by the full bundle iff it is forced by the forgotten one (`forget_exact`),
equivalently certified against one iff against the other (`forget_certified`), and the change
is conservative (`forget_conservative`).  `SeedStatics.project` on a bundle's system is the
projection onto one coordinate (`project_iff_projection`); projections compose
(`projection_comp`).

§2.  **A settled coordinate may be forgotten.**  If coordinate `k` is settled, the rows
specialized at that settlement and restricted to the other coordinates (`dropCoord`) give the
projection of the forced region under every later docket state and every later settlement
(`forget_settled`).  **A live coordinate may not**: over `(X, Y)` with `P(Y) ≥ 3/4 · P(X)`,
forgetting `X` while it is unsettled leaves no constraint on `Y`; once `X` settles true the
full record forces `P(Y) ∈ [3/4, 1]`; forgetting `X` after it settles keeps that
(`live_forget_cost`).

§3.  **A closed account**: an account with no live port denotes the same resolution under every
later resolution of the ports, and every later substitution leaves its receipts and its
denotation unchanged (`closed_evaluate_const`, `closed_subst`).

§4.  **Loss as slack.**  Along a schedule of forgetting steps each differing from a reference
step on a set of worlds, the excess of a row at the final stage exceeds its excess under the
reference schedule by at most the row's oscillation times the sum over stages of the held
credence's mass on that stage's set (`schedule_slack`); the reference is exact forgetting when
its steps are maps of worlds, which the theorem does not require; where those masses are bounded by a summable sequence
the total is bounded uniformly in the number of stages (`schedule_bounded`,
`schedule_summable`).

§5.  **Choosing what to forget.**  Two records over `(φ, A, B)`, with the one obligation on
`φ` running through `A` in the first and through `B` in the second; one of `A`, `B` must be
dropped, and both then settle true.  Dropping the coordinate the obligation runs through
leaves `φ ∈ [0,1]` on both records; each coordinate fixed in advance leaves `φ ∈ [3/4, 1]` on
one of them, which is what the full record forces on both (`selective_forgetting`).

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.Recollection
import Workspace.Normativity.Contrib.IncompatibilitySemantics
import Workspace.Normativity.Contrib.AuthorityActivation

namespace Workspace.Normativity.Contrib.Forgetting

open Workspace.Normativity.Contrib.NormativeInductorComposition
open Workspace.Normativity.Contrib.SeedStatics
open Workspace.Normativity.Contrib.RowAlternative
open Workspace.Normativity.Contrib.Conservativity
open Workspace.Normativity.Contrib.IncompatibilitySemantics
open Workspace.Normativity.Contrib.FourierMotzkin
open Workspace.Normativity.Contrib.Recollection
open Finset

variable {d : ℕ}

/-! ## 1. Fourier–Motzkin elimination computes the projection -/

/-- A row over `d + 1` coordinates as a constraint with coordinate `k` in the last position. -/
def toLast (k : Fin (d + 1)) (r : Row (d + 1)) : LinCon :=
  (List.ofFn (Fin.snoc (fun j => r.a (k.succAbove j)) (r.a k) : Fin (d + 1) → ℚ), r.b, false)

lemma toLast_strict (k : Fin (d + 1)) (r : Row (d + 1)) : (toLast k r).strict = false := rfl

lemma toLast_const (k : Fin (d + 1)) (r : Row (d + 1)) : (toLast k r).const = r.b := rfl

lemma toLast_coeff (k : Fin (d + 1)) (r : Row (d + 1)) (i : Fin (d + 1)) :
    (toLast k r).coeffs.getD (i : ℕ) 0 =
      (Fin.snoc (fun j => r.a (k.succAbove j)) (r.a k) : Fin (d + 1) → ℚ) i := by
  show (List.ofFn (Fin.snoc (fun j => r.a (k.succAbove j)) (r.a k) : Fin (d + 1) → ℚ)).getD
    (i : ℕ) 0 = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos i.isLt]
  rfl

/-- The constraint holds at `(x, t)` iff the row holds at `x` with `t` inserted at `k`. -/
theorem toLast_sat (k : Fin (d + 1)) (r : Row (d + 1)) (x : Fin d → ℝ) (t : ℝ) :
    (toLast k r).Sat (Fin.snoc x t : Fin (d + 1) → ℝ) ↔
      r.SatR (Fin.insertNth k t x : Fin (d + 1) → ℝ) := by
  have hl : (toLast k r).eval (Fin.snoc x t : Fin (d + 1) → ℝ) =
      ∑ j, (r.a (k.succAbove j) : ℝ) * x j + (r.a k : ℝ) * t := by
    unfold LinCon.eval
    simp_rw [toLast_coeff]
    rw [Fin.sum_univ_castSucc]
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  have hr : ∑ i, (r.a i : ℝ) * (Fin.insertNth k t x : Fin (d + 1) → ℝ) i =
      (r.a k : ℝ) * t + ∑ j, (r.a (k.succAbove j) : ℝ) * x j := by
    rw [Fin.sum_univ_succAbove _ k]
    simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  unfold LinCon.Sat Row.SatR
  rw [toLast_strict]
  simp only [Bool.false_eq_true, if_false, toLast_const]
  rw [hl, hr, add_comm]

/-- A non-strict constraint over `d` coordinates as a row. -/
def ofLin (c : LinCon) : Row d := ⟨fun i => c.coeffs.getD (i : ℕ) 0, c.const⟩

theorem ofLin_satR (c : LinCon) (hc : c.strict = false) (x : Fin d → ℝ) :
    (ofLin c : Row d).SatR x ↔ c.Sat x := by
  unfold Row.SatR LinCon.Sat LinCon.eval ofLin
  rw [hc]
  simp

/-- **Eliminate coordinate `k`**: one Fourier–Motzkin step on the rows with `k` moved last. -/
def eliminate (k : Fin (d + 1)) (L : List (Row (d + 1))) : List (Row d) :=
  (elim d (L.map (toLast k))).map ofLin

/-- At real points the eliminated rows hold iff some value of coordinate `k` satisfies the
original rows. -/
theorem eliminate_satR (k : Fin (d + 1)) (L : List (Row (d + 1))) (x : Fin d → ℝ) :
    (∀ r ∈ eliminate k L, r.SatR x) ↔
      ∃ t : ℝ, ∀ r ∈ L, r.SatR (Fin.insertNth k t x : Fin (d + 1) → ℝ) := by
  have hns : NonStrict (elim d (L.map (toLast k))) := elim_nonStrict (by
    intro c hc
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 hc
    rfl)
  have h1 : (∀ r ∈ eliminate k L, r.SatR x) ↔
      FourierMotzkin.Sat (elim d (L.map (toLast k))) x := by
    unfold eliminate FourierMotzkin.Sat
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact forall₂_congr fun c hc => ofLin_satR c (hns c hc) x
  rw [h1, elim_sat_iff]
  refine exists_congr fun t => ?_
  unfold FourierMotzkin.Sat
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, toLast_sat]

/-- The rows fixing every coordinate but `k` at the values `x`. -/
def fixRows (k : Fin (d + 1)) (x : Fin d → ℚ) : List (Row (d + 1)) :=
  (List.finRange d).flatMap fun j =>
    [boundRow (k.succAbove j) 1 (x j), boundRow (k.succAbove j) (-1) (-(x j))]

/-- **Elimination computes the projection, at rational points**: the eliminated rows hold at
`x` iff `x` is the restriction of a rational solution of the original rows. -/
theorem eliminate_sat_iff (k : Fin (d + 1)) (L : List (Row (d + 1))) (x : Fin d → ℚ) :
    SatAll (eliminate k L) x ↔ projection k.succAbove (SatAll L) x := by
  constructor
  · intro h
    have hR : ∀ r ∈ eliminate k L, r.SatR (fun j => (x j : ℝ)) :=
      fun r hr => (sat_iff_satR r x).1 (h r hr)
    obtain ⟨t, ht⟩ := (eliminate_satR k L _).1 hR
    have hreal : ∃ z : Fin (d + 1) → ℝ, ∀ r ∈ L ++ fixRows k x, r.SatR z := by
      refine ⟨Fin.insertNth k t fun j => (x j : ℝ), fun r hr => ?_⟩
      rcases List.mem_append.1 hr with hr | hr
      · exact ht r hr
      · simp only [fixRows, List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons,
          List.not_mem_nil, or_false] at hr
        obtain ⟨j, rfl | rfl⟩ := hr
        · rw [boundRow_satR, Fin.insertNth_apply_succAbove]; push_cast; linarith
        · rw [boundRow_satR, Fin.insertNth_apply_succAbove]; push_cast; linarith
    obtain ⟨y, hy⟩ := exists_rat_of_real _ hreal
    rw [satAll_append] at hy
    refine ⟨y, hy.1, funext fun j => ?_⟩
    have h1 := hy.2 (boundRow (k.succAbove j) 1 (x j))
      (List.mem_flatMap.2 ⟨j, List.mem_finRange j, List.mem_cons_self⟩)
    have h2 := hy.2 (boundRow (k.succAbove j) (-1) (-(x j)))
      (List.mem_flatMap.2 ⟨j, List.mem_finRange j, List.mem_cons_of_mem _ List.mem_cons_self⟩)
    rw [boundRow_sat] at h1 h2
    show y (k.succAbove j) = x j
    linarith
  · rintro ⟨y, hy, rfl⟩ r hr
    refine (sat_iff_satR r _).2
      ((eliminate_satR k L fun j => ((y (k.succAbove j) : ℚ) : ℝ)).2 ⟨(y k : ℝ), fun r' hr' => ?_⟩
        r hr)
    have hcast : (Fin.insertNth k ((y k : ℚ) : ℝ) (fun j => ((y (k.succAbove j) : ℚ) : ℝ)) :
        Fin (d + 1) → ℝ) = fun i => ((y i : ℚ) : ℝ) :=
      Fin.insertNth_self_removeNth k fun i => ((y i : ℚ) : ℝ)
    rw [hcast]
    exact (sat_iff_satR r' y).1 (hy r' hr')

/-- **Forgetting coordinate `k` of a bundle**: the eliminated rows of the bundle and the cube,
as a bundle on the retained coordinates. -/
def forget {Q : Type*} (k : Fin (d + 1)) (B : Bundle Q (d + 1)) : Bundle Unit d :=
  (eliminate k (B.map CitedRow.row ++ cubeRows (d + 1))).map fun r => ⟨(), r⟩

/-- **The forgotten bundle's region is the projection of the bundle's region** along the
coordinate map that drops `k`. -/
theorem forget_region {Q : Type*} (k : Fin (d + 1)) (B : Bundle Q (d + 1)) (x : Fin d → ℚ) :
    (forget k B).Region x ↔ projection k.succAbove B.Region x := by
  have key : SatAll (eliminate k (B.map CitedRow.row ++ cubeRows (d + 1))) x ↔
      projection k.succAbove B.Region x := by
    rw [eliminate_sat_iff]
    exact exists_congr fun y => and_congr_left' (region_iff_satAll B y).symm
  have hrows : (∀ c ∈ forget k B, c.row.Sat x) ↔
      SatAll (eliminate k (B.map CitedRow.row ++ cubeRows (d + 1))) x := by
    unfold forget SatAll
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · exact fun hx => key.1 (hrows.1 hx.2)
  · intro hx
    refine ⟨?_, hrows.2 (key.2 hx)⟩
    obtain ⟨y, hy, rfl⟩ := hx
    exact fun j => hy.1 _

/-- **Forgetting is exact on the retained fragment**: a row over the retained coordinates is
forced by the full bundle iff it is forced by the forgotten one. -/
theorem forget_exact {Q : Type*} (k : Fin (d + 1)) (B : Bundle Q (d + 1)) (r : Row d) :
    Forces B.Region (Conservativity.pull (Translation.ofMap k.succAbove) r) ↔
      Forces (forget k B).Region r := by
  constructor
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := (forget_region k B x).1 hx
    exact (pull_ofMap_sat_iff _ r y).1 (h y hy)
  · intro h y hy
    exact (pull_ofMap_sat_iff _ r y).2 (h _ ((forget_region k B _).2 ⟨y, hy, rfl⟩))

/-- **Forgetting a coordinate is conservative on the retained fragment.** -/
theorem forget_conservative {Q : Type*} (k : Fin (d + 1)) (B : Bundle Q (d + 1)) :
    Conservative (Translation.ofMap k.succAbove) (forget k B).Region B.Region :=
  ⟨fun r h => (forget_exact k B r).2 h, fun r h => (forget_exact k B r).1 h⟩

theorem semEntails_iff_forces {Q : Type*} (B : Bundle Q d) (g : Row d) :
    SemEntails (B.map CitedRow.row) g ↔ Forces B.Region g := by
  unfold SemEntails Forces Bundle.Region SatAll
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

/-- **Exactness in the row logic**: a row over the retained coordinates has an entailment
certificate against the full bundle iff it has one against the forgotten bundle. -/
theorem forget_certified {Q : Type*} (k : Fin (d + 1)) (B : Bundle Q (d + 1)) (r : Row d) :
    CertEntails (B.map CitedRow.row) (Conservativity.pull (Translation.ofMap k.succAbove) r) ↔
      CertEntails ((forget k B).map CitedRow.row) r := by
  rw [certEntails_iff_sem, certEntails_iff_sem, semEntails_iff_forces, semEntails_iff_forces,
    forget_exact]

/-- Projections along coordinate maps compose. -/
theorem projection_comp {d₁ d₂ d₃ : ℕ} (e₁ : Fin d₂ → Fin d₃) (e₂ : Fin d₁ → Fin d₂)
    (R : (Fin d₃ → ℚ) → Prop) (x : Fin d₁ → ℚ) :
    projection e₂ (projection e₁ R) x ↔ projection (e₁ ∘ e₂) R x := by
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z ∘ e₁, ⟨z, hz, rfl⟩, rfl⟩

theorem regionR_of_region {Q : Type*} (B : Bundle Q d) {x : Fin d → ℚ} (hx : B.Region x) :
    B.RegionR fun i => (x i : ℝ) :=
  (regionR_iff_satR B _).2 fun r hr => (sat_iff_satR r x).1 ((region_iff_satAll B x).1 hx r hr)

/-- **`SeedStatics.project` is the projection onto one coordinate**: the one-dimensional system
it leaves holds at a rational value `v` iff some rational point of the bundle's region has
`φ`-coordinate `v`. -/
theorem project_iff_projection {Q : Type*} {m : ℕ} (φ : Fin (m + 1)) (B : Bundle Q (m + 1))
    (v : ℚ) :
    FourierMotzkin.Sat (project m (system φ B)) (fun _ : Fin 1 => (v : ℝ)) ↔
      projection (fun _ : Fin 1 => φ) B.Region fun _ => v := by
  rw [project_sat_iff]
  constructor
  · rintro ⟨z, hz, h0⟩
    rw [system_sat_iff] at hz
    obtain ⟨x, hx, hxφ⟩ := exists_rat_point_at B φ v
      ⟨z ∘ pos φ, hz, by simp only [Function.comp, pos_self]; exact h0⟩
    exact ⟨x, hx, funext fun _ => hxφ⟩
  · rintro ⟨x, hx, hxe⟩
    have hxφ : x φ = v := congrFun hxe 0
    refine ⟨(fun i => (x i : ℝ)) ∘ pos φ, (system_sat_iff φ B _).2 ?_, ?_⟩
    · have : ((fun i => (x i : ℝ)) ∘ pos φ) ∘ pos φ = fun i => (x i : ℝ) :=
        funext fun k => by simp [Function.comp, pos_pos]
      rw [this]
      exact regionR_of_region B hx
    · simp [Function.comp, pos_zero, hxφ]

/-! ## 2. A settled coordinate may be forgotten; a live one may not -/

/-- A row with coordinate `k` dropped. -/
def dropCoord (k : Fin (d + 1)) (r : Row (d + 1)) : Row d := ⟨fun j => r.a (k.succAbove j), r.b⟩

/-- A row that does not mention `k` holds at a point iff its restriction holds at the point's
restriction. -/
theorem dropCoord_sat (k : Fin (d + 1)) (r : Row (d + 1)) (hk : r.a k = 0)
    (y : Fin (d + 1) → ℚ) : (dropCoord k r).Sat (y ∘ k.succAbove) ↔ r.Sat y := by
  unfold Row.Sat dropCoord
  rw [Fin.sum_univ_succAbove (fun i => r.a i * y i) k, hk, zero_mul, zero_add]
  rfl

/-- A settlement restricted to the coordinates other than `k`. -/
def dropSettlement (k : Fin (d + 1)) (F : Settlement (d + 1)) : Settlement d :=
  ⟨fun j => F.val (k.succAbove j)⟩

/-- **Forgetting a settled coordinate.**  With `k` settled at `F`, the rows specialized at `F`
and restricted to the other coordinates give the projection of the forced region under every
docket state and every later settlement: the retained rows, their ports and ids, and the later
settlement on the retained coordinates are all that is read. -/
theorem forget_settled {A : Type*} (S : Seed (d + 1) A) (W : List (SubItem (d + 1)))
    (st : DocketState) {F F' : Settlement (d + 1)} (k : Fin (d + 1)) {b : Bool}
    (hk : F.val k = some b) (hF : F.le F') (x : Fin d → ℚ) :
    projection k.succAbove (forcedRegion S W st F') x ↔
      InCube x ∧ (dropSettlement k F').Pinned x ∧
      (∀ it ∈ S.liveSub st ++ W, (dropCoord k (specialize F it.form.row)).Sat x) ∧
      (∀ it ∈ S.liveStr st, (dropCoord k (specialize F it.row)).Sat x) := by
  have hzero : ∀ r : Row (d + 1), (specialize F r).a k = 0 := fun r => by simp [specialize, hk]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [forcedRegion_iff] at hy
    obtain ⟨hcube, hpin, hsub, hstr⟩ := hy
    refine ⟨fun j => hcube _, fun j b' hj => hpin _ b' hj, fun it hit => ?_, fun it hit => ?_⟩
    · exact (dropCoord_sat k _ (hzero _) y).2
        ((specialize_sat_iff F _ (hpin.mono hF)).2 (hsub it hit))
    · exact (dropCoord_sat k _ (hzero _) y).2
        ((specialize_sat_iff F _ (hpin.mono hF)).2 (hstr it hit))
  · rintro ⟨hcube, hpin, hsub, hstr⟩
    have hk' : F'.val k = some b := hF k b hk
    obtain ⟨y, hy, hyk⟩ : ∃ y : Fin (d + 1) → ℚ, y ∘ k.succAbove = x ∧ y k = truth b :=
      ⟨Fin.insertNth k (truth b) x, funext fun j => by simp, by simp⟩
    subst hy
    have hpin' : F'.Pinned y := by
      intro i b' hi
      rcases Fin.eq_self_or_eq_succAbove k i with rfl | ⟨j, rfl⟩
      · rw [hyk, Option.some.inj (hk'.symm.trans hi)]
      · exact hpin j b' hi
    refine ⟨y, (forcedRegion_iff S W st F' y).2 ⟨fun i => ?_, hpin', fun it hit => ?_,
      fun it hit => ?_⟩, rfl⟩
    · rcases Fin.eq_self_or_eq_succAbove k i with rfl | ⟨j, rfl⟩
      · rw [hyk]; cases b <;> simp [truth]
      · exact hcube j
    · exact (specialize_sat_iff F _ (hpin'.mono hF)).1
        ((dropCoord_sat k _ (hzero _) y).1 (hsub it hit))
    · exact (specialize_sat_iff F _ (hpin'.mono hF)).1
        ((dropCoord_sat k _ (hzero _) y).1 (hstr it hit))

/-- The seed over `(X, Y)` with the one item `P(Y) ≥ 3/4 · P(X)`. -/
def liveSeed : Seed 2 Unit := ⟨[⟨Form.strength 0 1 (3/4), 0⟩], [], ⟨∅, ∅⟩⟩

/-- `X` settled true. -/
def settledX : Settlement 2 := ⟨![some true, none]⟩

lemma liveSeed_region (F : Settlement 2) (y : Fin 2 → ℚ) :
    forcedRegion liveSeed [] DocketState.quiet F y ↔
      InCube y ∧ F.Pinned y ∧ 3/4 * y 0 ≤ y 1 := by
  rw [forcedRegion_iff]
  simp [liveSeed, Seed.liveSub, Seed.liveStr, DocketState.quiet, Form.strength_sat_iff]

/-- The hypotheses of `forget_settled` inhabited: `X` settled true in `liveSeed`. -/
theorem forget_settled_witness (x : Fin 1 → ℚ) :
    projection (0 : Fin 2).succAbove (forcedRegion liveSeed [] DocketState.quiet settledX) x ↔
      InCube x ∧ (dropSettlement 0 settledX).Pinned x ∧
      (∀ it ∈ liveSeed.liveSub DocketState.quiet ++ [],
        (dropCoord 0 (specialize settledX it.form.row)).Sat x) ∧
      (∀ it ∈ liveSeed.liveStr DocketState.quiet,
        (dropCoord 0 (specialize settledX it.row)).Sat x) :=
  forget_settled liveSeed [] DocketState.quiet 0 (b := true) rfl (Settlement.le_refl _) x

lemma succAbove_zero_two : ((0 : Fin 2).succAbove : Fin 1 → Fin 2) = fun _ => 1 := by
  funext j; fin_cases j; rfl

/-- **The cost of forgetting a live coordinate.**  Forgetting `X` while it is unsettled leaves
the whole cube on `Y`; once `X` settles true the full record's forced interval for `Y` is
`[3/4, 1]`; forgetting `X` after it has settled keeps `P(Y) ≥ 3/4`. -/
theorem live_forget_cost :
    (∀ x : Fin 1 → ℚ,
      projection (0 : Fin 2).succAbove
        (forcedRegion liveSeed [] DocketState.quiet (Settlement.empty 2)) x ↔ InCube x) ∧
    IsForcedInterval liveSeed [] DocketState.quiet settledX 1 (3/4) 1 ∧
    (∀ x : Fin 1 → ℚ,
      projection (0 : Fin 2).succAbove (forcedRegion liveSeed [] DocketState.quiet settledX) x ↔
        InCube x ∧ 3/4 ≤ x 0) := by
  have hpinX : ∀ y : Fin 2 → ℚ, settledX.Pinned y ↔ y 0 = 1 := by
    intro y
    constructor
    · intro h
      have := h 0 true rfl
      simpa [truth] using this
    · intro h i b hi
      fin_cases i
      · have hb : b = true := by simpa [settledX] using hi.symm
        subst hb
        simpa [truth] using h
      · simp [settledX] at hi
  refine ⟨fun x => ?_, ⟨?_, ?_, ?_, ?_⟩, fun x => ?_⟩
  · rw [succAbove_zero_two]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact fun j => ((liveSeed_region _ y).1 hy).1 _
    · intro hx
      refine ⟨![0, x 0], (liveSeed_region _ _).2 ⟨fun i => ?_, Settlement.empty_pinned _, ?_⟩, ?_⟩
      · fin_cases i
        · simp
        · simpa using hx 0
      · simpa using (hx 0).1
      · funext j; fin_cases j; rfl
  · intro y hy
    obtain ⟨-, hpin, hrow⟩ := (liveSeed_region _ y).1 hy
    rw [(hpinX y).1 hpin] at hrow
    linarith
  · intro y hy
    exact (((liveSeed_region _ y).1 hy).1 1).2
  · exact ⟨![1, 3/4], by decide +kernel, rfl⟩
  · exact ⟨![1, 1], by decide +kernel, rfl⟩
  · rw [succAbove_zero_two]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hcube, hpin, hrow⟩ := (liveSeed_region _ y).1 hy
      rw [(hpinX y).1 hpin] at hrow
      exact ⟨fun j => hcube _, by simp only [Function.comp]; linarith⟩
    · rintro ⟨hx, h34⟩
      refine ⟨![1, x 0], (liveSeed_region _ _).2 ⟨fun i => ?_, (hpinX _).2 rfl, ?_⟩, ?_⟩
      · fin_cases i
        · simp
        · simpa using hx 0
      · simpa using h34
      · funext j; fin_cases j; rfl

/-! ## 4. Loss as slack along a forgetting schedule -/

section Schedule

variable {n : ℕ → ℕ}

theorem push_ofMap_id {m : ℕ} (q : Fin m → ℚ) :
    (Recollection.ofMap (fun w : Fin m => w)).push q = q := by
  funext w
  simp [Recollection.push, Translation.apply, Recollection.toTranslation, Recollection.ofMap]

/-- **A forgetting schedule composed**: `K t` retells the stage-`t` worlds as the
stage-`t + 1` worlds; the chain retells the first worlds as the stage-`T` worlds. -/
def chain (K : ∀ t, Recollection (n (t + 1)) (n t)) : ∀ T, Recollection (n T) (n 0)
  | 0 => Recollection.ofMap fun w => w
  | T + 1 => (K T).comp (chain K T)

theorem chain_push_nonneg (K : ∀ t, Recollection (n (t + 1)) (n t)) {q : Fin (n 0) → ℚ}
    (hq : ∀ w, 0 ≤ q w) : ∀ T w, 0 ≤ (chain K T).push q w
  | 0, w => by rw [chain, push_ofMap_id]; exact hq w
  | T + 1, w => by
      rw [chain, Recollection.push_comp]
      exact Recollection.push_nonneg _ (chain_push_nonneg K hq T) w

/-- The accumulated mass: the sum over stages `t < T` of the mass the credence held at stage
`t` places on that stage's set `B t`. -/
def scheduleLoss (K : ∀ t, Recollection (n (t + 1)) (n t)) (B : ∀ t, Finset (Fin (n t)))
    (q : Fin (n 0) → ℚ) : ℕ → ℚ
  | 0 => 0
  | T + 1 => scheduleLoss K B q T + ∑ w ∈ B T, (chain K T).push q w

/-- **Forgetting with loss composes as slack.**  If each step `K t` agrees with a reference
step `K₀ t` off the set `B t`, then at every stage a row with coefficients in `[lo, hi]` has
excess at the held credence at most its excess under the reference schedule plus `(hi − lo)`
times the accumulated mass. -/
theorem schedule_slack (K K₀ : ∀ t, Recollection (n (t + 1)) (n t))
    (B : ∀ t, Finset (Fin (n t))) (hB : ∀ t w, w ∉ B t → (K t).k w = (K₀ t).k w) (lo hi : ℚ)
    (q : Fin (n 0) → ℚ) (hq : ∀ w, 0 ≤ q w) :
    ∀ T (r : Row (n T)), (∀ i, lo ≤ r.a i ∧ r.a i ≤ hi) →
      excess r ((chain K T).push q) ≤
        excess r ((chain K₀ T).push q) + (hi - lo) * scheduleLoss K B q T := by
  intro T
  induction T with
  | zero =>
    intro r _
    simp [chain, scheduleLoss]
  | succ T ih =>
    intro r hr
    have h1 := approx_step (K T) (K₀ T) (B T) (hB T) r lo hi hr ((chain K T).push q)
      (chain_push_nonneg K hq T)
    have hr' : ∀ i, lo ≤ ((K₀ T).pull r).a i ∧ ((K₀ T).pull r).a i ≤ hi :=
      fun i => retold_bounds (K₀ T) r hr i
    have h2 := ih ((K₀ T).pull r) hr'
    rw [excess_pull, excess_pull] at h2
    have hsplit : (hi - lo) * scheduleLoss K B q (T + 1) =
        (hi - lo) * scheduleLoss K B q T + (hi - lo) * ∑ w ∈ B T, (chain K T).push q w := by
      rw [scheduleLoss, mul_add]
    rw [chain, chain, Recollection.push_comp, Recollection.push_comp, hsplit]
    linarith

theorem scheduleLoss_le (K : ∀ t, Recollection (n (t + 1)) (n t)) (B : ∀ t, Finset (Fin (n t)))
    (q : Fin (n 0) → ℚ) (ε : ℕ → ℚ) (hε : ∀ t, ∑ w ∈ B t, (chain K t).push q w ≤ ε t) :
    ∀ T, scheduleLoss K B q T ≤ ∑ t ∈ Finset.range T, ε t
  | 0 => by simp [scheduleLoss]
  | T + 1 => by
      rw [scheduleLoss, Finset.sum_range_succ]
      exact add_le_add (scheduleLoss_le K B q ε hε T) (hε T)

/-- **A schedule whose stage masses have bounded partial sums loses a bounded amount in
total**, uniformly in the number of stages. -/
theorem schedule_bounded (K K₀ : ∀ t, Recollection (n (t + 1)) (n t))
    (B : ∀ t, Finset (Fin (n t))) (hB : ∀ t w, w ∉ B t → (K t).k w = (K₀ t).k w) (lo hi : ℚ)
    (hlohi : lo ≤ hi) (q : Fin (n 0) → ℚ) (hq : ∀ w, 0 ≤ q w) (ε : ℕ → ℚ) (E : ℚ)
    (hε : ∀ t, ∑ w ∈ B t, (chain K t).push q w ≤ ε t)
    (hE : ∀ T, ∑ t ∈ Finset.range T, ε t ≤ E) :
    ∀ T (r : Row (n T)), (∀ i, lo ≤ r.a i ∧ r.a i ≤ hi) →
      excess r ((chain K T).push q) ≤ excess r ((chain K₀ T).push q) + (hi - lo) * E := by
  intro T r hr
  have h := schedule_slack K K₀ B hB lo hi q hq T r hr
  have hle : scheduleLoss K B q T ≤ E := (scheduleLoss_le K B q ε hε T).trans (hE T)
  have := mul_le_mul_of_nonneg_left hle (sub_nonneg.2 hlohi)
  linarith

/-- **Summable slack.**  Where the stage masses are bounded by a summable sequence, the total
loss is at most the row's oscillation times its sum, at every stage. -/
theorem schedule_summable (K K₀ : ∀ t, Recollection (n (t + 1)) (n t))
    (B : ∀ t, Finset (Fin (n t))) (hB : ∀ t w, w ∉ B t → (K t).k w = (K₀ t).k w) (lo hi : ℚ)
    (hlohi : lo ≤ hi) (q : Fin (n 0) → ℚ) (hq : ∀ w, 0 ≤ q w) (ε : ℕ → ℚ) (hε0 : ∀ t, 0 ≤ ε t)
    (hsum : Summable fun t => (ε t : ℝ))
    (hε : ∀ t, ∑ w ∈ B t, (chain K t).push q w ≤ ε t) :
    ∀ T (r : Row (n T)), (∀ i, lo ≤ r.a i ∧ r.a i ≤ hi) →
      ((excess r ((chain K T).push q) : ℚ) : ℝ) ≤
        ((excess r ((chain K₀ T).push q) : ℚ) : ℝ) + ((hi - lo : ℚ) : ℝ) * ∑' t, (ε t : ℝ) := by
  intro T r hr
  have h := schedule_slack K K₀ B hB lo hi q hq T r hr
  have hle := scheduleLoss_le K B q ε hε T
  have h1 : ((scheduleLoss K B q T : ℚ) : ℝ) ≤ ∑' t, (ε t : ℝ) := by
    calc ((scheduleLoss K B q T : ℚ) : ℝ) ≤ ((∑ t ∈ Finset.range T, ε t : ℚ) : ℝ) := by
          exact_mod_cast hle
      _ = ∑ t ∈ Finset.range T, (ε t : ℝ) := by push_cast; rfl
      _ ≤ ∑' t, (ε t : ℝ) :=
          hsum.sum_le_tsum (Finset.range T) fun t _ => by exact_mod_cast hε0 t
  have hR : ((excess r ((chain K T).push q) : ℚ) : ℝ) ≤
      ((excess r ((chain K₀ T).push q) : ℚ) : ℝ) +
        ((hi - lo : ℚ) : ℝ) * ((scheduleLoss K B q T : ℚ) : ℝ) := by
    exact_mod_cast h
  have hnn : (0 : ℝ) ≤ ((hi - lo : ℚ) : ℝ) := by exact_mod_cast sub_nonneg.2 hlohi
  have := mul_le_mul_of_nonneg_left h1 hnn
  linarith

/-- The hypotheses of `schedule_slack` inhabited: two worlds at every stage, each step
retelling both worlds as the first where the reference step is the identity, so that the steps
differ on the second world; the row `P(S) ≥ 1/2`; two stages from the credence `(1/2, 1/2)`. -/
theorem schedule_slack_witness :
    excess (atLeast (1/2))
        ((chain (n := fun _ => 2) (fun _ => Recollection.ofMap ![0, 0]) 2).push ![1/2, 1/2]) ≤
      excess (atLeast (1/2))
        ((chain (n := fun _ => 2) (fun _ => Recollection.ofMap fun w => w) 2).push ![1/2, 1/2]) +
        (0 - (-1)) * scheduleLoss (n := fun _ => 2) (fun _ => Recollection.ofMap ![0, 0])
          (fun _ => {1}) ![1/2, 1/2] 2 :=
  schedule_slack (n := fun _ => 2) (fun _ => Recollection.ofMap ![0, 0])
    (fun _ => Recollection.ofMap fun w => w) (fun _ => {1})
    (fun _ w hw => by
      fin_cases w
      · rfl
      · exact absurd (Finset.mem_singleton_self _) hw)
    (-1) 0 ![1/2, 1/2] (fun w => by fin_cases w <;> norm_num) 2 (atLeast (1/2))
    (fun i => by fin_cases i <;> simp [atLeast])

end Schedule

/-! ## 5. Choosing what to forget -/

/-- The forced interval of a coordinate over a region: valid bounds, both attained. -/
def IsInterval {m : ℕ} (R : (Fin m → ℚ) → Prop) (φ : Fin m) (lo hi : ℚ) : Prop :=
  (∀ x, R x → lo ≤ x φ ∧ x φ ≤ hi) ∧ (∃ x, R x ∧ x φ = lo) ∧ ∃ x, R x ∧ x φ = hi

/-- The record over `(φ, A, B)` whose one obligation on `φ` runs through coordinate `a`:
`P(φ) ≥ 3/4 · P(a)`. -/
def recOn (a : Fin 3) : Seed 3 Unit := ⟨[⟨Form.strength a 0 (3/4), 0⟩], [], ⟨∅, ∅⟩⟩

lemma recOn_region (a : Fin 3) (F : Settlement 3) (y : Fin 3 → ℚ) :
    forcedRegion (recOn a) [] DocketState.quiet F y ↔
      InCube y ∧ F.Pinned y ∧ 3/4 * y a ≤ y 0 := by
  rw [forcedRegion_iff]
  simp [recOn, Seed.liveSub, Seed.liveStr, DocketState.quiet, Form.strength_sat_iff]

/-- Both `A` and `B` settle true. -/
def bothTrue : Settlement 3 := ⟨![none, some true, some true]⟩

/-- On the two retained coordinates: the retained one of `A`, `B` settles true. -/
def later : Settlement 2 := ⟨![none, some true]⟩

lemma succAbove_one_three : ((1 : Fin 3).succAbove : Fin 2 → Fin 3) = ![0, 2] := by
  funext j; fin_cases j <;> rfl

lemma succAbove_two_three : ((2 : Fin 3).succAbove : Fin 2 → Fin 3) = ![0, 1] := by
  funext j; fin_cases j <;> rfl

/-- `later` is the settlement `bothTrue` restricted to the retained coordinates, whichever of
`A`, `B` is dropped. -/
theorem later_eq : dropSettlement 1 bothTrue = later ∧ dropSettlement 2 bothTrue = later := by
  constructor
  · unfold dropSettlement later
    rw [succAbove_one_three]
    exact congrArg Settlement.mk (funext fun j => by fin_cases j <;> rfl)
  · unfold dropSettlement later
    rw [succAbove_two_three]
    exact congrArg Settlement.mk (funext fun j => by fin_cases j <;> rfl)

lemma later_pinned (x : Fin 2 → ℚ) : later.Pinned x ↔ x 1 = 1 := by
  constructor
  · intro h
    have := h 1 true rfl
    simpa [truth] using this
  · intro h i b hi
    fin_cases i
    · simp [later] at hi
    · have hb : b = true := by simpa [later] using hi.symm
      subst hb
      simpa [truth] using h

lemma bothTrue_pinned (y : Fin 3 → ℚ) : bothTrue.Pinned y ↔ y 1 = 1 ∧ y 2 = 1 := by
  constructor
  · intro h
    have h1 := h 1 true rfl
    have h2 := h 2 true rfl
    exact ⟨by simpa [truth] using h1, by simpa [truth] using h2⟩
  · rintro ⟨h1, h2⟩ i b hi
    fin_cases i
    · simp [bothTrue] at hi
    · have hb : b = true := by simpa [bothTrue] using hi.symm
      subst hb
      simpa [truth] using h1
    · have hb : b = true := by simpa [bothTrue] using hi.symm
      subst hb
      simpa [truth] using h2

/-- What a reasoner holds on the retained coordinates after dropping coordinate `k` of the
record `recOn a` and then recording the later settlement `F''`. -/
def afterForget (a k : Fin 3) (F'' : Settlement 2) (x : Fin 2 → ℚ) : Prop :=
  projection k.succAbove (forcedRegion (recOn a) [] DocketState.quiet (Settlement.empty 3)) x ∧
    F''.Pinned x

lemma inCube_three {a b c : ℚ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1) :
    InCube ![a, b, c] := by
  intro i
  fin_cases i
  · simpa using ha
  · simpa using hb
  · simpa using hc

/-- Dropping `A` from the record whose obligation runs through `A`. -/
lemma afterForget_AA (x : Fin 2 → ℚ) : afterForget 1 1 later x ↔ InCube x ∧ x 1 = 1 := by
  unfold afterForget
  rw [later_pinned, succAbove_one_three]
  refine and_congr_left fun _ => ⟨?_, fun hx => ?_⟩
  · rintro ⟨y, hy, rfl⟩
    have hc := ((recOn_region _ _ y).1 hy).1
    intro j
    fin_cases j
    · exact hc 0
    · exact hc 2
  · refine ⟨![x 0, 0, x 1], (recOn_region _ _ _).2
      ⟨inCube_three (hx 0) (by norm_num) (hx 1), Settlement.empty_pinned _, ?_⟩, ?_⟩
    · simpa using (hx 0).1
    · funext j; fin_cases j <;> rfl

/-- Dropping `B` from the record whose obligation runs through `B`. -/
lemma afterForget_BB (x : Fin 2 → ℚ) : afterForget 2 2 later x ↔ InCube x ∧ x 1 = 1 := by
  unfold afterForget
  rw [later_pinned, succAbove_two_three]
  refine and_congr_left fun _ => ⟨?_, fun hx => ?_⟩
  · rintro ⟨y, hy, rfl⟩
    have hc := ((recOn_region _ _ y).1 hy).1
    intro j
    fin_cases j
    · exact hc 0
    · exact hc 1
  · refine ⟨![x 0, x 1, 0], (recOn_region _ _ _).2
      ⟨inCube_three (hx 0) (hx 1) (by norm_num), Settlement.empty_pinned _, ?_⟩, ?_⟩
    · simpa using (hx 0).1
    · funext j; fin_cases j <;> rfl

/-- Dropping `A` from the record whose obligation runs through `B`. -/
lemma afterForget_BA (x : Fin 2 → ℚ) :
    afterForget 2 1 later x ↔ (InCube x ∧ 3/4 * x 1 ≤ x 0) ∧ x 1 = 1 := by
  unfold afterForget
  rw [later_pinned, succAbove_one_three]
  refine and_congr_left fun _ => ⟨?_, fun hx => ?_⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hc, -, hrow⟩ := (recOn_region _ _ y).1 hy
    refine ⟨fun j => ?_, hrow⟩
    fin_cases j
    · exact hc 0
    · exact hc 2
  · refine ⟨![x 0, 0, x 1], (recOn_region _ _ _).2
      ⟨inCube_three (hx.1 0) (by norm_num) (hx.1 1), Settlement.empty_pinned _, ?_⟩, ?_⟩
    · simpa using hx.2
    · funext j; fin_cases j <;> rfl

/-- Dropping `B` from the record whose obligation runs through `A`. -/
lemma afterForget_AB (x : Fin 2 → ℚ) :
    afterForget 1 2 later x ↔ (InCube x ∧ 3/4 * x 1 ≤ x 0) ∧ x 1 = 1 := by
  unfold afterForget
  rw [later_pinned, succAbove_two_three]
  refine and_congr_left fun _ => ⟨?_, fun hx => ?_⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hc, -, hrow⟩ := (recOn_region _ _ y).1 hy
    refine ⟨fun j => ?_, hrow⟩
    fin_cases j
    · exact hc 0
    · exact hc 1
  · refine ⟨![x 0, x 1, 0], (recOn_region _ _ _).2
      ⟨inCube_three (hx.1 0) (hx.1 1) (by norm_num), Settlement.empty_pinned _, ?_⟩, ?_⟩
    · simpa using hx.2
    · funext j; fin_cases j <;> rfl

lemma inCube_two {a b : ℚ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) : InCube ![a, b] := by
  intro i
  fin_cases i
  · simpa using ha
  · simpa using hb

lemma interval_free {R : (Fin 2 → ℚ) → Prop} (h : ∀ x, R x ↔ InCube x ∧ x 1 = 1) :
    IsInterval R 0 0 1 :=
  ⟨fun x hx => ((h x).1 hx).1 0,
    ⟨![0, 1], (h _).2 ⟨inCube_two (by norm_num) (by norm_num), rfl⟩, rfl⟩,
    ⟨![1, 1], (h _).2 ⟨inCube_two (by norm_num) (by norm_num), rfl⟩, rfl⟩⟩

lemma interval_bound {R : (Fin 2 → ℚ) → Prop}
    (h : ∀ x, R x ↔ (InCube x ∧ 3/4 * x 1 ≤ x 0) ∧ x 1 = 1) : IsInterval R 0 (3/4) 1 := by
  refine ⟨fun x hx => ?_, ⟨![3/4, 1], (h _).2 ⟨⟨inCube_two (by norm_num) (by norm_num), ?_⟩, rfl⟩,
    rfl⟩, ⟨![1, 1], (h _).2 ⟨⟨inCube_two (by norm_num) (by norm_num), ?_⟩, rfl⟩, rfl⟩⟩
  · obtain ⟨⟨hc, hrow⟩, h1⟩ := (h x).1 hx
    rw [h1] at hrow
    exact ⟨by linarith, (hc 0).2⟩
  · norm_num
  · norm_num

lemma recOn_full (a : Fin 3) (ha : a = 1 ∨ a = 2) :
    IsForcedInterval (recOn a) [] DocketState.quiet bothTrue 0 (3/4) 1 := by
  have hy : ∀ y : Fin 3 → ℚ, bothTrue.Pinned y → y a = 1 := by
    intro y hp
    obtain ⟨h1, h2⟩ := (bothTrue_pinned y).1 hp
    rcases ha with rfl | rfl
    · exact h1
    · exact h2
  refine ⟨fun y hy' => ?_, fun y hy' => ?_, ⟨![3/4, 1, 1], ?_, rfl⟩, ⟨![1, 1, 1], ?_, rfl⟩⟩
  · obtain ⟨-, hp, hrow⟩ := (recOn_region _ _ y).1 hy'
    rw [hy y hp] at hrow
    linarith
  · exact (((recOn_region _ _ y).1 hy').1 0).2
  · rcases ha with rfl | rfl <;> decide +kernel
  · rcases ha with rfl | rfl <;> decide +kernel

/-- **Choosing what to forget is steering.**  The choice made after seeing the record — drop
the coordinate the obligation runs through — leaves `φ` the interval `[0,1]` on both records;
each coordinate fixed in advance leaves `[3/4, 1]` on one of them; the full record forces
`[3/4, 1]` on both. -/
theorem selective_forgetting :
    (IsInterval (afterForget 1 1 later) 0 0 1 ∧ IsInterval (afterForget 2 2 later) 0 0 1) ∧
    (IsInterval (afterForget 2 1 later) 0 (3/4) 1 ∧ IsInterval (afterForget 1 2 later) 0 (3/4) 1) ∧
    (IsForcedInterval (recOn 1) [] DocketState.quiet bothTrue 0 (3/4) 1 ∧
      IsForcedInterval (recOn 2) [] DocketState.quiet bothTrue 0 (3/4) 1) :=
  ⟨⟨interval_free afterForget_AA, interval_free afterForget_BB⟩,
    ⟨interval_bound afterForget_BA, interval_bound afterForget_AB⟩,
    ⟨recOn_full 1 (Or.inl rfl), recOn_full 2 (Or.inr rfl)⟩⟩

end Workspace.Normativity.Contrib.Forgetting

/-! ## 3. A closed account -/

namespace Workspace.Normativity.Contrib.OccurrenceIntegrity.Program

universe u v w

variable {Occ : Type u} {Req : Type v} {S : Protocol.{u, v, w} Occ Req}
  {A B : Boundary Occ Req} {r : Req}

/-- **An account with no live port denotes one resolution**, whatever the ports resolve to. -/
theorem closed_evaluate_const (t : Program S B r) (ht : t.livePorts = 0)
    (v v' : (p : Fin B.portCount) → S.Resolution (B.demand p)) :
    t.evaluate v = t.evaluate v' := by
  induction t with
  | live p hp _ =>
      exfalso
      simp [livePorts] at ht
  | answer receipt historical => rfl
  | close receipt historical => rfl
  | combine law historical children ih =>
      simp only [evaluate]
      congr 1
      funext i
      refine ih i ?_
      simp only [livePorts] at ht
      exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Multiset.zero_le _).mp ht i
        (Finset.mem_univ _)

/-- **What persists of a closed account.**  Every later substitution leaves an account with no
live port with the same receipts, no live port, and the same denotation. -/
theorem closed_subst (hab : A.history <+: B.history)
    (replacement : (p : Fin A.portCount) → Program S B (A.demand p))
    (t : Program S A r) (ht : t.livePorts = 0) :
    (t.subst hab replacement).terminals = t.terminals ∧
      (t.subst hab replacement).livePorts = 0 ∧
      ∀ v v₀, (t.subst hab replacement).evaluate v = t.evaluate v₀ := by
  refine ⟨?_, ?_, fun v v₀ => ?_⟩
  · rw [terminals_subst, ht]; simp
  · rw [livePorts_subst, ht]; simp
  · rw [evaluate_subst]
    exact closed_evaluate_const t ht _ _

end Workspace.Normativity.Contrib.OccurrenceIntegrity.Program

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.Forgetting.toLast
#print axioms Workspace.Normativity.Contrib.Forgetting.toLast_strict
#print axioms Workspace.Normativity.Contrib.Forgetting.toLast_const
#print axioms Workspace.Normativity.Contrib.Forgetting.toLast_coeff
#print axioms Workspace.Normativity.Contrib.Forgetting.toLast_sat
#print axioms Workspace.Normativity.Contrib.Forgetting.ofLin
#print axioms Workspace.Normativity.Contrib.Forgetting.ofLin_satR
#print axioms Workspace.Normativity.Contrib.Forgetting.eliminate
#print axioms Workspace.Normativity.Contrib.Forgetting.eliminate_satR
#print axioms Workspace.Normativity.Contrib.Forgetting.fixRows
#print axioms Workspace.Normativity.Contrib.Forgetting.eliminate_sat_iff
#print axioms Workspace.Normativity.Contrib.Forgetting.forget
#print axioms Workspace.Normativity.Contrib.Forgetting.forget_region
#print axioms Workspace.Normativity.Contrib.Forgetting.forget_exact
#print axioms Workspace.Normativity.Contrib.Forgetting.forget_conservative
#print axioms Workspace.Normativity.Contrib.Forgetting.semEntails_iff_forces
#print axioms Workspace.Normativity.Contrib.Forgetting.forget_certified
#print axioms Workspace.Normativity.Contrib.Forgetting.projection_comp
#print axioms Workspace.Normativity.Contrib.Forgetting.regionR_of_region
#print axioms Workspace.Normativity.Contrib.Forgetting.project_iff_projection
#print axioms Workspace.Normativity.Contrib.Forgetting.dropCoord
#print axioms Workspace.Normativity.Contrib.Forgetting.dropCoord_sat
#print axioms Workspace.Normativity.Contrib.Forgetting.dropSettlement
#print axioms Workspace.Normativity.Contrib.Forgetting.forget_settled
#print axioms Workspace.Normativity.Contrib.Forgetting.liveSeed
#print axioms Workspace.Normativity.Contrib.Forgetting.settledX
#print axioms Workspace.Normativity.Contrib.Forgetting.liveSeed_region
#print axioms Workspace.Normativity.Contrib.Forgetting.forget_settled_witness
#print axioms Workspace.Normativity.Contrib.Forgetting.succAbove_zero_two
#print axioms Workspace.Normativity.Contrib.Forgetting.live_forget_cost
#print axioms Workspace.Normativity.Contrib.Forgetting.push_ofMap_id
#print axioms Workspace.Normativity.Contrib.Forgetting.chain
#print axioms Workspace.Normativity.Contrib.Forgetting.chain_push_nonneg
#print axioms Workspace.Normativity.Contrib.Forgetting.scheduleLoss
#print axioms Workspace.Normativity.Contrib.Forgetting.schedule_slack
#print axioms Workspace.Normativity.Contrib.Forgetting.scheduleLoss_le
#print axioms Workspace.Normativity.Contrib.Forgetting.schedule_bounded
#print axioms Workspace.Normativity.Contrib.Forgetting.schedule_summable
#print axioms Workspace.Normativity.Contrib.Forgetting.schedule_slack_witness
#print axioms Workspace.Normativity.Contrib.Forgetting.IsInterval
#print axioms Workspace.Normativity.Contrib.Forgetting.recOn
#print axioms Workspace.Normativity.Contrib.Forgetting.recOn_region
#print axioms Workspace.Normativity.Contrib.Forgetting.bothTrue
#print axioms Workspace.Normativity.Contrib.Forgetting.later
#print axioms Workspace.Normativity.Contrib.Forgetting.succAbove_one_three
#print axioms Workspace.Normativity.Contrib.Forgetting.succAbove_two_three
#print axioms Workspace.Normativity.Contrib.Forgetting.later_eq
#print axioms Workspace.Normativity.Contrib.Forgetting.later_pinned
#print axioms Workspace.Normativity.Contrib.Forgetting.bothTrue_pinned
#print axioms Workspace.Normativity.Contrib.Forgetting.afterForget
#print axioms Workspace.Normativity.Contrib.Forgetting.inCube_three
#print axioms Workspace.Normativity.Contrib.Forgetting.afterForget_AA
#print axioms Workspace.Normativity.Contrib.Forgetting.afterForget_BB
#print axioms Workspace.Normativity.Contrib.Forgetting.afterForget_BA
#print axioms Workspace.Normativity.Contrib.Forgetting.afterForget_AB
#print axioms Workspace.Normativity.Contrib.Forgetting.inCube_two
#print axioms Workspace.Normativity.Contrib.Forgetting.interval_free
#print axioms Workspace.Normativity.Contrib.Forgetting.interval_bound
#print axioms Workspace.Normativity.Contrib.Forgetting.recOn_full
#print axioms Workspace.Normativity.Contrib.Forgetting.selective_forgetting
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.closed_evaluate_const
#print axioms Workspace.Normativity.Contrib.OccurrenceIntegrity.Program.closed_subst
