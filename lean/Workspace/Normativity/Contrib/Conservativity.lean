/-
# Conservativity of a vocabulary change on the old fragment

Round `projects/normativity/rounds/2026-11-08-content-recollection/`, matter 1.

A **translation** (§1) gives each old coordinate as a rational linear form in the new
coordinates; a coordinate map `e : Fin d → Fin d'` is the `0/1` case (`Translation.ofMap`).
An old row pulls back to a new row (`pull`, `pull_sat_iff`), and a new region has an image on
the old coordinates (`image`); for a coordinate map the image is the projection `y ∘ e`
(`projection`) and the pullback is the row transport of the seed-statics branch's unlanded §9
(`pull_ofMap_sat_iff`; item 122).

Against an old region `R` and a new region `R'`, the new **refines** the old when the pullback
of every row the old region forces is forced by the new, and **adds nothing** when every old
row whose pullback the new region forces was already forced by the old.  Both are stated on
rows, so neither mentions a point of the other vocabulary.  §2 proves:

* `refines_iff` — refinement iff the image of the new region lies in the old region;
* `addsNothing_iff` — adding nothing iff the old region lies in the image, by the rational
  alternative (`RowAlternative.alternative_family`): a point outside the image is cut off by a
  row whose pullback is a nonnegative combination of the new region's rows;
* `conservative_iff` — both together iff the image equals the old region.

§3 defines the extension of a seed along a coordinate map by new items (`extend`) and proves
that an extension always refines (`extend_refines`), so for an extension conservativity is that
every old forced point lifts (`extend_conservative_iff`).  Injectivity of `e` is used nowhere.

§4, two fixtures.  `ext₁`: a new coordinate with an applicability row and a coherence row over
`P(X) ≥ 1/2`, conservative.  `ext₂`: a new term `T` with an introduction row
`P(T) ≥ 4/5 · P(X)` and an elimination row `P(Y) ≥ 3/4 · P(T)` over the seed `P(X) ≥ 1/2` on
`(X, Y)`; together they force `P(Y) ≥ 3/10`, which the old seed does not (`badCert`,
`bad_forces_lower`, `bad_lower_attained`, `bad_not_conservative`); with the elimination row's
port defeated the extension is conservative again (`bad_conservative_when_defeated`).

§5.  `SeedStatics.seed_independence_strict` is not an instance: read with the identity map,
it says a nonempty strict layer adds no *pin* (`strict_layer_adds_no_pin`), and a strict layer
does add rows (`strict_layer_adds_rows`).

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.RowAlternative

namespace Workspace.Normativity.Contrib.Conservativity

open Workspace.Normativity.Contrib.NormativeInductorComposition
open Workspace.Normativity.Contrib.SeedStatics
open Workspace.Normativity.Contrib.RowAlternative
open Finset

variable {d d' : ℕ}

/-! ## 1. Translations, pullback, image -/

/-- A **translation** of the new vocabulary into the old: old coordinate `i` is the linear form
`∑ j, T i j * y j` in the new coordinates. -/
abbrev Translation (d d' : ℕ) := Fin d → Fin d' → ℚ

/-- The old price vector a new price vector induces. -/
def Translation.apply (T : Translation d d') (y : Fin d' → ℚ) : Fin d → ℚ :=
  fun i => ∑ j, T i j * y j

/-- The translation of a coordinate map: old coordinate `i` is new coordinate `e i`. -/
def Translation.ofMap (e : Fin d → Fin d') : Translation d d' := fun i j => if e i = j then 1 else 0

@[simp] theorem Translation.ofMap_apply (e : Fin d → Fin d') (y : Fin d' → ℚ) :
    (Translation.ofMap e).apply y = y ∘ e := by
  funext i
  simp [Translation.apply, Translation.ofMap]

/-- **The pullback of an old row** along a translation: a row over the new coordinates. -/
def pull (T : Translation d d') (r : Row d) : Row d' := ⟨fun j => ∑ i, r.a i * T i j, r.b⟩

/-- The pullback holds at a new point iff the row holds at the induced old point. -/
theorem pull_sat_iff (T : Translation d d') (r : Row d) (y : Fin d' → ℚ) :
    (pull T r).Sat y ↔ r.Sat (T.apply y) := by
  have h : ∑ j, (∑ i, r.a i * T i j) * y j = ∑ i, r.a i * ∑ j, T i j * y j := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  unfold Row.Sat pull Translation.apply
  simp only [h]

/-- The pullback along a coordinate map holds at a new point iff the row holds at the point's
restriction to the old coordinates. -/
theorem pull_ofMap_sat_iff (e : Fin d → Fin d') (r : Row d) (y : Fin d' → ℚ) :
    (pull (Translation.ofMap e) r).Sat y ↔ r.Sat (y ∘ e) := by
  rw [pull_sat_iff, Translation.ofMap_apply]

/-- A region **forces** a row: the row holds at every point of it. -/
def Forces (R : (Fin d → ℚ) → Prop) (r : Row d) : Prop := ∀ x, R x → r.Sat x

/-- The image of a new region on the old coordinates. -/
def image (T : Translation d d') (R' : (Fin d' → ℚ) → Prop) : (Fin d → ℚ) → Prop :=
  fun x => ∃ y, R' y ∧ T.apply y = x

/-- **The projection of a new region onto the old coordinates** along a coordinate map. -/
def projection (e : Fin d → Fin d') (R' : (Fin d' → ℚ) → Prop) : (Fin d → ℚ) → Prop :=
  fun x => ∃ y, R' y ∧ y ∘ e = x

theorem image_ofMap (e : Fin d → Fin d') (R' : (Fin d' → ℚ) → Prop) :
    image (Translation.ofMap e) R' = projection e R' := by
  funext x
  simp [image, projection]

/-- **Refinement**: the new region keeps every commitment of the old — the pullback of every
row the old region forces is forced by the new. -/
def Refines (T : Translation d d') (R : (Fin d → ℚ) → Prop) (R' : (Fin d' → ℚ) → Prop) : Prop :=
  ∀ r : Row d, Forces R r → Forces R' (pull T r)

/-- **Adds nothing**: the new region commits to nothing in the old vocabulary the old region
did not — every old row whose pullback the new region forces is forced by the old. -/
def AddsNothing (T : Translation d d') (R : (Fin d → ℚ) → Prop) (R' : (Fin d' → ℚ) → Prop) :
    Prop :=
  ∀ r : Row d, Forces R' (pull T r) → Forces R r

/-- **Conservative** on the old fragment: a refinement that adds nothing. -/
def Conservative (T : Translation d d') (R : (Fin d → ℚ) → Prop) (R' : (Fin d' → ℚ) → Prop) :
    Prop :=
  Refines T R R' ∧ AddsNothing T R R'

/-! ## 2. The theorems -/

section Theorems

variable {Q Q' : Type*}

/-- **Refinement iff the image lies in the old region.** -/
theorem refines_iff (T : Translation d d') (B : Bundle Q d) (R' : (Fin d' → ℚ) → Prop) :
    Refines T B.Region R' ↔ ∀ x, image T R' x → B.Region x := by
  constructor
  · rintro h x ⟨y, hy, rfl⟩
    refine ⟨(cubeRows_sat_iff _).1 fun r hr => ?_, fun c hc => ?_⟩
    · exact (pull_sat_iff T r y).1
        (h r (fun x hx => (cubeRows_sat_iff x).2 hx.1 r hr) y hy)
    · exact (pull_sat_iff T c.row y).1 (h c.row (fun x hx => hx.2 c hc) y hy)
  · intro h r hr y hy
    exact (pull_sat_iff T r y).2 (hr _ (h _ ⟨y, hy, rfl⟩))

/-- The rows cutting out "a point of the new region whose image is `x`": the new bundle's rows,
the cube rows, and for each old coordinate the two rows fixing its linear form at `x i`. -/
def liftRows (T : Translation d d') (B' : Bundle Q' d') (x : Fin d → ℚ) :
    Fin (B'.map CitedRow.row ++ cubeRows d').length ⊕ (Fin d ⊕ Fin d) → Row d'
  | .inl k => (B'.map CitedRow.row ++ cubeRows d').get k
  | .inr (.inl i) => ⟨fun j => T i j, x i⟩
  | .inr (.inr i) => ⟨fun j => -T i j, -x i⟩

lemma liftRows_sat_iff (T : Translation d d') (B' : Bundle Q' d') (x : Fin d → ℚ)
    (y : Fin d' → ℚ) :
    (∀ i, (liftRows T B' x i).Sat y) ↔ B'.Region y ∧ T.apply y = x := by
  rw [region_iff_satAll, satAll_iff_get]
  constructor
  · intro h
    refine ⟨fun k => h (.inl k), funext fun i => ?_⟩
    have h1 := h (.inr (.inl i))
    have h2 := h (.inr (.inr i))
    unfold Row.Sat liftRows at h1 h2
    simp only [neg_mul, Finset.sum_neg_distrib] at h2
    unfold Translation.apply
    linarith
  · rintro ⟨h, rfl⟩ (k | i | i)
    · exact h k
    · unfold Row.Sat liftRows Translation.apply; exact le_rfl
    · unfold Row.Sat liftRows Translation.apply
      simp only [neg_mul, Finset.sum_neg_distrib]
      exact le_rfl

/-- **A point outside the image is cut off by a row the new region forces after pullback.** -/
theorem separating_row (T : Translation d d') (B' : Bundle Q' d') (x : Fin d → ℚ)
    (hx : ¬ image T B'.Region x) :
    ∃ r : Row d, Forces B'.Region (pull T r) ∧ ¬ r.Sat x := by
  have hno : ¬ ∃ y, ∀ i, (liftRows T B' x i).Sat y := by
    rintro ⟨y, hy⟩
    exact hx ⟨y, (liftRows_sat_iff T B' x y).1 hy⟩
  obtain ⟨u, hu0, hc, hb⟩ := (alternative_family (liftRows T B' x)).1 hno
  simp only [Fintype.sum_sum_type, liftRows] at hc hb
  let w : Weights (B'.map CitedRow.row ++ cubeRows d') := ⟨fun k => u (.inl k), fun k => hu0 _⟩
  refine ⟨⟨fun i => u (.inr (.inr i)) - u (.inr (.inl i)), w.const⟩, ?_, ?_⟩
  · intro y hy
    have hsum := w.sum_le ((region_iff_satAll B' y).1 hy)
    have hco : ∀ j, (∑ i, (u (.inr (.inr i)) - u (.inr (.inl i))) * T i j) = w.coeff j := by
      intro j
      have hj := hc j
      simp only [mul_neg, Finset.sum_neg_distrib] at hj
      have : ∑ i, (u (.inr (.inr i)) - u (.inr (.inl i))) * T i j
          = ∑ i, u (.inr (.inr i)) * T i j - ∑ i, u (.inr (.inl i)) * T i j := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this]
      show _ = ∑ k, u (.inl k) * _
      linarith
    unfold Row.Sat pull
    simp only [hco]
    exact hsum
  · unfold Row.Sat
    simp only [not_le]
    have hb' : w.const + (∑ i, u (.inr (.inl i)) * x i + ∑ i, u (.inr (.inr i)) * -x i) < 0 := hb
    have : ∑ i, (u (.inr (.inr i)) - u (.inr (.inl i))) * x i
        = ∑ i, u (.inr (.inr i)) * x i - ∑ i, u (.inr (.inl i)) * x i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    simp only [mul_neg, Finset.sum_neg_distrib] at hb'
    linarith

/-- **Adding nothing iff the old region lies in the image.** -/
theorem addsNothing_iff (T : Translation d d') (R : (Fin d → ℚ) → Prop) (B' : Bundle Q' d') :
    AddsNothing T R B'.Region ↔ ∀ x, R x → image T B'.Region x := by
  constructor
  · intro h x hx
    by_contra hno
    obtain ⟨r, hr, hrx⟩ := separating_row T B' x hno
    exact hrx (h r hr x hx)
  · intro h r hr x hx
    obtain ⟨y, hy, rfl⟩ := h x hx
    exact (pull_sat_iff T r y).1 (hr y hy)

/-- **Conservative iff the image of the new region equals the old region.** -/
theorem conservative_iff (T : Translation d d') (B : Bundle Q d) (B' : Bundle Q' d') :
    Conservative T B.Region B'.Region ↔ ∀ x, image T B'.Region x ↔ B.Region x := by
  unfold Conservative
  rw [refines_iff, addsNothing_iff]
  exact ⟨fun h x => ⟨h.1 x, h.2 x⟩, fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩⟩

end Theorems

/-! ## 3. The extension of a seed along a coordinate map -/

/-- A leverage form relabelled along a coordinate map. -/
def mapForm (e : Fin d → Fin d') : Form d → Form d'
  | .premise X c => .premise (e X) c
  | .applicability X XA c => .applicability (e X) (e XA) c
  | .strength XA XAY c => .strength (e XA) (e XAY) c

/-- The relabelled form's row holds at a new point iff the form's row holds at its projection. -/
theorem mapForm_sat_iff (e : Fin d → Fin d') (f : Form d) (y : Fin d' → ℚ) :
    (mapForm e f).row.Sat y ↔ f.row.Sat (y ∘ e) := by
  cases f <;>
    simp [mapForm, Form.premise_sat_iff, Form.applicability_sat_iff, Form.strength_sat_iff]

/-- A substantive item relabelled, on its own port. -/
def mapSub (e : Fin d → Fin d') (it : SubItem d) : SubItem d' := ⟨mapForm e it.form, it.port⟩

/-- A structural item relabelled: its row pulled back along the coordinate map. -/
def mapStr (e : Fin d → Fin d') (it : StrItem d) : StrItem d' :=
  ⟨pull (Translation.ofMap e) it.row, it.kind, it.id⟩

/-- **The extension of a seed along a coordinate map** by new substantive and structural
items: every old item relabelled, the new items beside them. -/
def extend {A : Type*} (e : Fin d → Fin d') (S : Seed d A) (sub' : List (SubItem d'))
    (str' : List (StrItem d')) : Seed d' A :=
  ⟨S.sub.map (mapSub e) ++ sub', S.str.map (mapStr e) ++ str',
    ⟨S.con.standing, S.con.protectedClass.image e⟩⟩

/-- A new settlement agrees with the old one on the old coordinates. -/
def SettlementExtends (e : Fin d → Fin d') (F : Settlement d) (F' : Settlement d') : Prop :=
  ∀ i, F'.val (e i) = F.val i

/-- **An extension refines**: every point of the extension's forced region projects into the
old forced region, under the same docket and a settlement agreeing on the old coordinates. -/
theorem extend_projects {A : Type*} (e : Fin d → Fin d') (S : Seed d A) (sub' : List (SubItem d'))
    (str' : List (StrItem d')) (W : List (SubItem d)) (st : DocketState) {F : Settlement d}
    {F' : Settlement d'} (hF : SettlementExtends e F F') {y : Fin d' → ℚ}
    (hy : forcedRegion (extend e S sub' str') (W.map (mapSub e)) st F' y) :
    forcedRegion S W st F (y ∘ e) := by
  rw [forcedRegion_iff] at hy ⊢
  obtain ⟨hcube, hpin, hsub, hstr⟩ := hy
  refine ⟨fun i => hcube (e i), fun i b hi => hpin (e i) b ((hF i).trans hi), ?_, ?_⟩
  · intro it hit
    rw [← mapForm_sat_iff]
    refine hsub (mapSub e it) ?_
    rcases List.mem_append.1 hit with h | h
    · refine List.mem_append.2 (Or.inl ?_)
      simp only [Seed.liveSub, extend, List.mem_filter, List.mem_append, List.mem_map,
        decide_eq_true_eq] at h ⊢
      exact ⟨Or.inl ⟨it, h.1, rfl⟩, h.2⟩
    · exact List.mem_append.2 (Or.inr (List.mem_map.2 ⟨it, h, rfl⟩))
  · intro it hit
    have := hstr (mapStr e it) (by
      simp only [Seed.liveStr, extend, List.mem_filter, List.mem_append, List.mem_map,
        decide_eq_true_eq] at hit ⊢
      exact ⟨Or.inl ⟨it, hit.1, rfl⟩, hit.2⟩)
    simpa [mapStr, pull_sat_iff] using this

theorem extend_refines {A : Type*} (e : Fin d → Fin d') (S : Seed d A) (sub' : List (SubItem d'))
    (str' : List (StrItem d')) (W : List (SubItem d)) (st : DocketState) {F : Settlement d}
    {F' : Settlement d'} (hF : SettlementExtends e F F') :
    Refines (Translation.ofMap e) (forcedRegion S W st F)
      (forcedRegion (extend e S sub' str') (W.map (mapSub e)) st F') := by
  refine (refines_iff _ (forcedBundle S W st F) _).2 ?_
  rintro x ⟨y, hy, rfl⟩
  rw [Translation.ofMap_apply]
  exact extend_projects e S sub' str' W st hF hy

/-- **Conservativity of an extension**: an extension is conservative on the old fragment iff
the projection of its forced region equals the old forced region, iff every old forced point
lifts. -/
theorem extend_conservative_iff {A : Type*} (e : Fin d → Fin d') (S : Seed d A)
    (sub' : List (SubItem d')) (str' : List (StrItem d')) (W : List (SubItem d))
    (st : DocketState) {F : Settlement d} {F' : Settlement d'} (hF : SettlementExtends e F F') :
    (Conservative (Translation.ofMap e) (forcedRegion S W st F)
        (forcedRegion (extend e S sub' str') (W.map (mapSub e)) st F') ↔
      ∀ x, projection e (forcedRegion (extend e S sub' str') (W.map (mapSub e)) st F') x ↔
        forcedRegion S W st F x) ∧
    ((∀ x, projection e (forcedRegion (extend e S sub' str') (W.map (mapSub e)) st F') x ↔
        forcedRegion S W st F x) ↔
      ∀ x, forcedRegion S W st F x →
        ∃ y, forcedRegion (extend e S sub' str') (W.map (mapSub e)) st F' y ∧ y ∘ e = x) := by
  refine ⟨?_, ?_⟩
  · have := conservative_iff (Translation.ofMap e) (forcedBundle S W st F)
      (forcedBundle (extend e S sub' str') (W.map (mapSub e)) st F')
    rw [image_ofMap] at this
    exact this
  · constructor
    · exact fun h x hx => (h x).2 hx
    · intro h x
      refine ⟨?_, h x⟩
      rintro ⟨y, hy, rfl⟩
      exact extend_projects e S sub' str' W st hF hy

/-! ## 4. Fixtures -/

theorem settlementExtends_empty (e : Fin d → Fin d') :
    SettlementExtends e (Settlement.empty d) (Settlement.empty d') := fun _ => rfl

/-! ### A conservative extension -/

/-- The old seed: `P(X) ≥ 1/2` on one coordinate. -/
def seed₁ : Seed 1 Unit := ⟨[⟨Form.premise 0 (1/2), 0⟩], [], ⟨∅, ∅⟩⟩

/-- The old coordinate `X` is new coordinate `0`. -/
def e₁ : Fin 1 → Fin 2 := fun _ => 0

/-- The new coordinate is `X ∧ A`: an applicability row `P(X∧A) ≥ 3/4 · P(X)` and the coherence
row `P(X∧A) ≤ P(X)`. -/
def ext₁ : Seed 2 Unit :=
  extend e₁ seed₁ [⟨Form.applicability 0 1 (3/4), 1⟩] [⟨⟨![-1, 1], 0⟩, .coherence, 0⟩]

/-- **The first fixture is conservative**: the projection of the extension's forced region is
the old forced region. -/
theorem ext₁_conservative :
    Conservative (Translation.ofMap e₁)
      (forcedRegion seed₁ [] DocketState.quiet (Settlement.empty 1))
      (forcedRegion ext₁ [] DocketState.quiet (Settlement.empty 2)) := by
  have key := extend_conservative_iff e₁ seed₁ [⟨Form.applicability 0 1 (3/4), 1⟩]
    [⟨⟨![-1, 1], 0⟩, .coherence, 0⟩] [] DocketState.quiet (settlementExtends_empty e₁)
  refine key.1.2 (key.2.2 ?_)
  intro x hx
  rw [forcedRegion_iff] at hx
  obtain ⟨hcube, -, hsub, -⟩ := hx
  have h0 := (Form.premise_sat_iff _ _ _).1
    (hsub ⟨Form.premise 0 (1/2), 0⟩ (by simp [seed₁, Seed.liveSub, DocketState.quiet]))
  refine ⟨![x 0, x 0], ?_, ?_⟩
  · show forcedRegion ext₁ [] DocketState.quiet (Settlement.empty 2) _
    rw [forcedRegion_iff]
    refine ⟨?_, Settlement.empty_pinned _, ?_, ?_⟩
    · intro i; fin_cases i <;> exact hcube 0
    · intro it hit
      simp only [ext₁, extend, seed₁, Seed.liveSub, DocketState.quiet, List.map_cons,
        List.map_nil, List.append_nil, List.cons_append, List.nil_append, mapSub, mapForm,
        List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hit
      rcases hit.1 with rfl | rfl
      · rw [Form.premise_sat_iff]; simpa [e₁] using h0
      · rw [Form.applicability_sat_iff]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        have := (hcube 0).1
        nlinarith
    · intro it hit
      simp only [ext₁, extend, seed₁, Seed.liveStr, DocketState.quiet, List.map_nil,
        List.nil_append, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hit
      rw [hit.1]
      simp [Row.Sat, Fin.sum_univ_two]
  · funext i
    fin_cases i
    simp [e₁]

/-! ### The bad concept -/

/-- The old seed: `P(X) ≥ 1/2` on the coordinates `(X, Y)`. -/
def seed₂ : Seed 2 Unit := ⟨[⟨Form.premise 0 (1/2), 0⟩], [], ⟨∅, ∅⟩⟩

/-- `X` and `Y` keep their places; the new term `T` is coordinate `2`. -/
def e₂ : Fin 2 → Fin 3 := ![0, 1]

/-- The introduction row of `T`, `P(T) ≥ 4/5 · P(X)`, on port `1`. -/
def intro : SubItem 3 := ⟨Form.applicability 0 2 (4/5), 1⟩

/-- The elimination row of `T`, `P(Y) ≥ 3/4 · P(T)`, on port `2`. -/
def elim : SubItem 3 := ⟨Form.strength 2 1 (3/4), 2⟩

/-- The extension by the new term with both rows. -/
def ext₂ : Seed 3 Unit := extend e₂ seed₂ [intro, elim] []

lemma ext₂_sub : ext₂.sub = [⟨Form.premise 0 (1/2), 0⟩, intro, elim] := by
  simp [ext₂, extend, seed₂, mapSub, mapForm, e₂]

/-- **The certificate of the forced bound**: `3/5` of the premise row, `3/4` of the
introduction row and the elimination row sum to `−P(Y) ≤ −3/10`. -/
def badCert : BoundCert 3 3 1 (-1) where
  mult := ![3/5, 3/4, 1]
  row := ![(Form.premise 0 (1/2) : Form 3).row, intro.form.row, elim.form.row]
  mult_nonneg := fun i => by fin_cases i <;> norm_num
  coeff_sum := fun j => by
    fin_cases j <;> simp [Fin.sum_univ_three, Form.row, intro, elim] <;> norm_num

theorem badCert_value : badCert.value = -(3/10) := by
  simp [BoundCert.value, badCert, Fin.sum_univ_three, Form.row, intro, elim]
  norm_num

/-- **The extension forces `P(Y) ≥ 3/10`**, by the certificate. -/
theorem bad_forces_lower :
    LowerBound ext₂ [] DocketState.quiet (Settlement.empty 3) 1 (3/10) := by
  intro y hy
  rw [forcedRegion_iff] at hy
  have hsub : ∀ it ∈ ext₂.sub, it.form.row.Sat y := fun it hit =>
    hy.2.2.1 it (by simpa [Seed.liveSub, DocketState.quiet] using hit)
  rw [ext₂_sub] at hsub
  have h0 : (Form.premise 0 (1/2) : Form 3).row.Sat y :=
    hsub ⟨Form.premise 0 (1/2), 0⟩ List.mem_cons_self
  have h1 : intro.form.row.Sat y := hsub intro (List.mem_cons_of_mem _ List.mem_cons_self)
  have h2 : elim.form.row.Sat y :=
    hsub elim (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have := badCert.sound y (fun i => by
    fin_cases i
    · simpa [badCert] using h0
    · simpa [badCert] using h1
    · simpa [badCert] using h2)
  rw [badCert_value] at this
  linarith

/-- The bound is attained: `(1/2, 3/10, 2/5)` lies in the extension's forced region. -/
theorem bad_lower_attained :
    forcedRegion ext₂ [] DocketState.quiet (Settlement.empty 3) ![1/2, 3/10, 2/5] := by
  decide +kernel

/-- **The old seed does not force it**: `(1/2, 0)` lies in the old forced region. -/
theorem old_not_forces_lower :
    ¬ LowerBound seed₂ [] DocketState.quiet (Settlement.empty 2) 1 (3/10) := by
  intro h
  have hx : forcedRegion seed₂ [] DocketState.quiet (Settlement.empty 2) ![1/2, 0] := by
    decide +kernel
  have := h _ hx
  norm_num at this

/-- **The second fixture refines and is not conservative**: the introduction and elimination
rows of the new term together commit the old fragment to the row `−P(Y) ≤ −3/10`. -/
theorem bad_not_conservative :
    Refines (Translation.ofMap e₂)
        (forcedRegion seed₂ [] DocketState.quiet (Settlement.empty 2))
        (forcedRegion ext₂ [] DocketState.quiet (Settlement.empty 3)) ∧
      ¬ AddsNothing (Translation.ofMap e₂)
        (forcedRegion seed₂ [] DocketState.quiet (Settlement.empty 2))
        (forcedRegion ext₂ [] DocketState.quiet (Settlement.empty 3)) := by
  refine ⟨extend_refines e₂ seed₂ [intro, elim] [] [] DocketState.quiet
    (settlementExtends_empty e₂), ?_⟩
  intro h
  have hold := h ⟨![0, -1], -(3/10)⟩ (fun y hy => by
    rw [pull_sat_iff, Translation.ofMap_apply]
    have := bad_forces_lower y hy
    simp only [Row.Sat, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Function.comp_apply, e₂]
    linarith)
  have hx : forcedRegion seed₂ [] DocketState.quiet (Settlement.empty 2) ![1/2, 0] := by
    decide +kernel
  have := hold _ hx
  simp [Row.Sat, Fin.sum_univ_two] at this
  norm_num at this

/-- **With the elimination row's port defeated the extension is conservative.** -/
theorem bad_conservative_when_defeated :
    Conservative (Translation.ofMap e₂)
      (forcedRegion seed₂ [] ⟨{2}, ∅⟩ (Settlement.empty 2))
      (forcedRegion ext₂ [] ⟨{2}, ∅⟩ (Settlement.empty 3)) := by
  have key := extend_conservative_iff e₂ seed₂ [intro, elim] [] [] ⟨{2}, ∅⟩
    (settlementExtends_empty e₂)
  refine key.1.2 (key.2.2 ?_)
  intro x hx
  rw [forcedRegion_iff] at hx
  obtain ⟨hcube, -, hsub, -⟩ := hx
  have h0 := (Form.premise_sat_iff _ _ _).1
    (hsub ⟨Form.premise 0 (1/2), 0⟩ (by simp [seed₂, Seed.liveSub]))
  refine ⟨![x 0, x 1, 1], ?_, ?_⟩
  · show forcedRegion ext₂ [] ⟨{2}, ∅⟩ (Settlement.empty 3) _
    rw [forcedRegion_iff]
    refine ⟨?_, Settlement.empty_pinned _, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact hcube 0
      · exact hcube 1
      · simp
    · intro it hit
      simp only [List.append_nil, Seed.liveSub, ext₂_sub, List.mem_filter, List.mem_cons,
        List.not_mem_nil, or_false, decide_eq_true_eq, Finset.mem_singleton] at hit
      rcases hit with ⟨rfl | rfl | rfl, hport⟩
      · rw [Form.premise_sat_iff]; simpa using h0
      · show (Form.applicability 0 2 (4/5) : Form 3).row.Sat _
        rw [Form.applicability_sat_iff]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        have := (hcube 0).2
        linarith
      · exact absurd rfl hport
    · intro it hit
      simp [ext₂, extend, seed₂, Seed.liveStr] at hit
  · funext i
    fin_cases i <;> simp [e₂]

/-! ## 5. Seed-independence is conservativity on pins only -/

/-- `seed_independence_strict` with the identity map and an empty second layer: **a nonempty
strict layer adds no pin**. -/
theorem strict_layer_adds_no_pin {Q : Type*} (B : Bundle Q d) (L : List (Row d)) (φ : Fin d)
    (p : ℝ) (hne : ∃ x, B.RegionR x ∧ ∀ r ∈ L, StrictSatR r x)
    (hpin : ∀ x, B.RegionR x → (∀ r ∈ L, StrictSatR r x) → x φ = p) :
    ∀ x, B.RegionR x → x φ = p :=
  fun x hx => seed_independence_strict B L [] φ p hne hpin x hx (by simp)

/-- **A strict layer adds rows**: over the cube on one coordinate, the strict layer `x < 1/2`
is nonempty and forces the row `x ≤ 1/2`, which the cube does not. -/
theorem strict_layer_adds_rows :
    ∃ (B : Bundle Unit 1) (L : List (Row 1)) (r : Row 1),
      (∃ x, B.RegionR x ∧ ∀ r' ∈ L, StrictSatR r' x) ∧
      (∀ x, B.RegionR x → (∀ r' ∈ L, StrictSatR r' x) → r.SatR x) ∧
      ¬ ∀ x, B.RegionR x → r.SatR x := by
  refine ⟨[], [⟨![1], 1/2⟩], ⟨![1], 1/2⟩, ⟨fun _ => 0, ?_, ?_⟩, ?_, ?_⟩
  · exact ⟨fun _ => by norm_num, fun _ h => by simp at h⟩
  · intro r' hr'
    simp only [List.mem_singleton] at hr'
    subst hr'
    simp [StrictSatR]
  · intro x _ hL
    have := hL ⟨![1], 1/2⟩ (by simp)
    simp only [StrictSatR, Row.SatR] at this ⊢
    exact this.le
  · intro h
    have := h (fun _ => 1) ⟨fun _ => by norm_num, fun _ hc => by simp at hc⟩
    simp [Row.SatR] at this
    norm_num at this

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.Conservativity.Translation.apply
#print axioms Workspace.Normativity.Contrib.Conservativity.Translation.ofMap
#print axioms Workspace.Normativity.Contrib.Conservativity.Translation.ofMap_apply
#print axioms Workspace.Normativity.Contrib.Conservativity.pull
#print axioms Workspace.Normativity.Contrib.Conservativity.pull_sat_iff
#print axioms Workspace.Normativity.Contrib.Conservativity.pull_ofMap_sat_iff
#print axioms Workspace.Normativity.Contrib.Conservativity.Forces
#print axioms Workspace.Normativity.Contrib.Conservativity.image
#print axioms Workspace.Normativity.Contrib.Conservativity.projection
#print axioms Workspace.Normativity.Contrib.Conservativity.image_ofMap
#print axioms Workspace.Normativity.Contrib.Conservativity.Refines
#print axioms Workspace.Normativity.Contrib.Conservativity.AddsNothing
#print axioms Workspace.Normativity.Contrib.Conservativity.Conservative
#print axioms Workspace.Normativity.Contrib.Conservativity.refines_iff
#print axioms Workspace.Normativity.Contrib.Conservativity.liftRows
#print axioms Workspace.Normativity.Contrib.Conservativity.liftRows_sat_iff
#print axioms Workspace.Normativity.Contrib.Conservativity.separating_row
#print axioms Workspace.Normativity.Contrib.Conservativity.addsNothing_iff
#print axioms Workspace.Normativity.Contrib.Conservativity.conservative_iff
#print axioms Workspace.Normativity.Contrib.Conservativity.mapForm
#print axioms Workspace.Normativity.Contrib.Conservativity.mapForm_sat_iff
#print axioms Workspace.Normativity.Contrib.Conservativity.mapSub
#print axioms Workspace.Normativity.Contrib.Conservativity.mapStr
#print axioms Workspace.Normativity.Contrib.Conservativity.extend
#print axioms Workspace.Normativity.Contrib.Conservativity.SettlementExtends
#print axioms Workspace.Normativity.Contrib.Conservativity.extend_projects
#print axioms Workspace.Normativity.Contrib.Conservativity.extend_refines
#print axioms Workspace.Normativity.Contrib.Conservativity.extend_conservative_iff
#print axioms Workspace.Normativity.Contrib.Conservativity.settlementExtends_empty
#print axioms Workspace.Normativity.Contrib.Conservativity.seed₁
#print axioms Workspace.Normativity.Contrib.Conservativity.e₁
#print axioms Workspace.Normativity.Contrib.Conservativity.ext₁
#print axioms Workspace.Normativity.Contrib.Conservativity.ext₁_conservative
#print axioms Workspace.Normativity.Contrib.Conservativity.seed₂
#print axioms Workspace.Normativity.Contrib.Conservativity.e₂
#print axioms Workspace.Normativity.Contrib.Conservativity.intro
#print axioms Workspace.Normativity.Contrib.Conservativity.elim
#print axioms Workspace.Normativity.Contrib.Conservativity.ext₂
#print axioms Workspace.Normativity.Contrib.Conservativity.ext₂_sub
#print axioms Workspace.Normativity.Contrib.Conservativity.badCert
#print axioms Workspace.Normativity.Contrib.Conservativity.badCert_value
#print axioms Workspace.Normativity.Contrib.Conservativity.bad_forces_lower
#print axioms Workspace.Normativity.Contrib.Conservativity.bad_lower_attained
#print axioms Workspace.Normativity.Contrib.Conservativity.old_not_forces_lower
#print axioms Workspace.Normativity.Contrib.Conservativity.bad_not_conservative
#print axioms Workspace.Normativity.Contrib.Conservativity.bad_conservative_when_defeated
#print axioms Workspace.Normativity.Contrib.Conservativity.strict_layer_adds_no_pin
#print axioms Workspace.Normativity.Contrib.Conservativity.strict_layer_adds_rows

end Workspace.Normativity.Contrib.Conservativity
