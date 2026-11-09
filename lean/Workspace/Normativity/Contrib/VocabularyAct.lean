/-
# A vocabulary change as an act on the docket: licence, challenge, and three readings

Round `projects/normativity/rounds/2026-11-08-content-recollection/`, follow-up of 2026-11-09,
matter 4, to fixture level.

§1.  A **vocabulary change** (`VocabularyChange`) is a docket occurrence: its owner, the
translation, the old and the new commitments as rows, and a declared protected fragment of old
rows.  Its **licence** (`Licensed`) is a refinement certificate on the fragment: for each
protected row and each old cube row, an entailment certificate of its pullback against the new
commitments.  A **challenge** (`Challenge`) is a broken-commitment witness as data: a row, an
entailment certificate of it against a list of old rows, and a point of the new region at which
its pullback fails; its validity is decidable (`Challenge.Valid`).  A valid challenge is a
broken commitment and every broken commitment has one (`Challenge.sound`, `challenge_complete`);
a licence exists iff the change refines the fragment (`licensed_iff_refines`); **a licensed
change admits no valid challenge on the protected fragment** (`licensed_no_challenge`) and an
unlicensed one admits one (`unlicensed_has_challenge`).  For a change that adds one coordinate,
adding nothing is a finite family of certificates as well: one for each row Fourier–Motzkin
elimination leaves (`addsNothing_certified`).  On the split fixture a change protecting the
credence rows alone is licensed and the commitment `P(S) ≥ 1/2` outside the fragment is
validly challenged (`split_licensed`, `splitChallenge_valid`).

§2.  **Three readings of a broken commitment**, as predicates on a recollection, a list of old
commitments and a new region: it **bars** the change (`Bars`); it is **accounted**, its loss
charged as slack (`Accounted`); or the **split** — a commitment whose obligation is live bars,
any other is accounted (`Split`).  The **charge** of a commitment (`Charge`) is the largest
excess of its pullback over the new region; each reading's verdict on one commitment is a
function of its charge (`readings_of_charge`).  Charges: the split fixture, `1/10`
(`split_charge`); abandonment, `13/20`, and at least `3/20` at every credence
(`abandon_charge`); a commitment with a live obligation, `P(X∧Y) ≥ 3/4 · P(X)` with `X`
unsettled, under a change that drops `X` — retold as a fair coin, `3/8`; retold as false, `0`,
so that all three readings admit the change at no charge (`half_charge`, `zero_charge`,
`zero_admitted`), and once `X` settles true the pin `P(X) ≥ 1` is charged `1/2` and `1` at
every new credence (`half_pin_charge`, `zero_pin_charge`).  No reading is adopted here.

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.Forgetting
import Workspace.Normativity.Contrib.WarrantEntitlement

namespace Workspace.Normativity.Contrib.VocabularyAct

open Workspace.Normativity.Contrib.NormativeInductorComposition
open Workspace.Normativity.Contrib.SeedStatics
open Workspace.Normativity.Contrib.RowAlternative
open Workspace.Normativity.Contrib.Conservativity
open Workspace.Normativity.Contrib.IncompatibilitySemantics
open Workspace.Normativity.Contrib.Recollection
open Workspace.Normativity.Contrib.Forgetting
open Finset

variable {d d' : ℕ}

/-! ## 1. The occurrence, its licence and its challenge -/

/-- The cube points of a list of rows. -/
def regionOf {m : ℕ} (L : List (Row m)) (x : Fin m → ℚ) : Prop := InCube x ∧ SatAll L x

theorem semEntails_iff_forces_regionOf {m : ℕ} (L : List (Row m)) (g : Row m) :
    SemEntails L g ↔ Forces (regionOf L) g := by
  unfold SemEntails Forces regionOf
  exact ⟨fun h x hx => h x hx.1 hx.2, fun h x hc hx => h x ⟨hc, hx⟩⟩

theorem regionOf_bundle {Q : Type*} {m : ℕ} (B : Bundle Q m) (x : Fin m → ℚ) :
    regionOf (B.map CitedRow.row) x ↔ B.Region x := by
  unfold regionOf Bundle.Region SatAll
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

/-- A **broken commitment** along a translation: a row the old region forces whose pullback
the new region does not.  `Recollection.Broken` is the case of a recollection's translation. -/
def BrokenAlong (T : Translation d d') (R : (Fin d → ℚ) → Prop) (R' : (Fin d' → ℚ) → Prop)
    (r : Row d) : Prop :=
  Forces R r ∧ ¬ Forces R' (Conservativity.pull T r)

theorem broken_iff_brokenAlong {n n' : ℕ} (K : Recollection n n') (R : (Fin n → ℚ) → Prop)
    (R' : (Fin n' → ℚ) → Prop) (r : Row n) :
    Broken K R R' r ↔ BrokenAlong K.toTranslation R R' r :=
  Iff.rfl

/-- **A vocabulary change as a docket occurrence**: its owner, the translation, the old and
the new commitments, and the declared protected fragment of old rows. -/
structure VocabularyChange (A : Type*) (d d' : ℕ) where
  owner : A
  T : Translation d d'
  old : List (Row d)
  new : List (Row d')
  fragment : List (Row d)

variable {A : Type*}

/-- **The licence**: a refinement certificate on the protected fragment — for every protected
row and every old cube row, an entailment certificate of its pullback against the new
commitments. -/
def Licensed (V : VocabularyChange A d d') : Prop :=
  ∀ p, Allowed V.fragment p → CertEntails V.new (Conservativity.pull V.T p)

/-- **A licence exists iff the change refines the protected fragment.** -/
theorem licensed_iff_refines (V : VocabularyChange A d d') :
    Licensed V ↔ Refines V.T (regionOf V.fragment) (regionOf V.new) := by
  constructor
  · intro h r hr y hy
    have hpush : regionOf V.fragment (V.T.apply y) := by
      have hall : ∀ p, Allowed V.fragment p → p.Sat (V.T.apply y) := fun p hp =>
        (pull_sat_iff V.T p y).1
          ((semEntails_iff_forces_regionOf _ _).1 ((certEntails_iff_sem _ _).1 (h p hp)) y hy)
      refine ⟨(cubeRows_sat_iff _).1 fun p hp => hall p ?_, fun p hp => hall p (Or.inl hp)⟩
      exact Or.inr ((mem_cubeRows p).1 hp)
    exact (pull_sat_iff V.T r y).2 (hr _ hpush)
  · intro h p hp
    refine (certEntails_iff_sem _ _).2 ((semEntails_iff_forces_regionOf _ _).2 (h p ?_))
    intro x hx
    rcases hp with hp | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact hx.2 p hp
    · exact cubeUpper_sat hx.1 i
    · exact cubeLower_sat hx.1 i

/-- **A challenge**: a broken-commitment witness as data — a row, an entailment certificate of
it, and a point of the new vocabulary. -/
structure Challenge (d d' : ℕ) where
  row : Row d
  m : ℕ
  cert : EntailCert d m row
  point : Fin d' → ℚ

/-- **A challenge is valid** against a change and a list `Γ` of old rows: the certificate
weights only rows allowed against `Γ`, the point is a cube point of the new commitments, and
the row's pullback fails there. -/
def Challenge.Valid (c : Challenge d d') (V : VocabularyChange A d d') (Γ : List (Row d)) : Prop :=
  (∀ i, Allowed Γ (c.cert.row i)) ∧ InCube c.point ∧ SatAll V.new c.point ∧
    ¬ (Conservativity.pull V.T c.row).Sat c.point

instance (c : Challenge d d') (V : VocabularyChange A d d') (Γ : List (Row d)) :
    Decidable (c.Valid V Γ) := by
  unfold Challenge.Valid Allowed
  infer_instance

/-- **A valid challenge is a broken commitment.** -/
theorem Challenge.sound {c : Challenge d d'} {V : VocabularyChange A d d'} {Γ : List (Row d)}
    (h : c.Valid V Γ) : BrokenAlong V.T (regionOf Γ) (regionOf V.new) c.row :=
  ⟨(semEntails_iff_forces_regionOf _ _).1 (certEntails_sem ⟨c.m, c.cert, h.1⟩),
    fun hf => h.2.2.2 (hf c.point ⟨h.2.1, h.2.2.1⟩)⟩

/-- **Every broken commitment has a valid challenge.** -/
theorem challenge_complete (V : VocabularyChange A d d') (Γ : List (Row d)) (r : Row d)
    (h : BrokenAlong V.T (regionOf Γ) (regionOf V.new) r) :
    ∃ c : Challenge d d', c.Valid V Γ ∧ c.row = r := by
  obtain ⟨m, cert, hall⟩ := (certEntails_iff_sem Γ r).2 ((semEntails_iff_forces_regionOf _ _).2 h.1)
  obtain ⟨y, hy⟩ := not_forall.1 h.2
  obtain ⟨hy, hfail⟩ := Classical.not_imp.1 hy
  exact ⟨⟨r, m, cert, y⟩, ⟨hall, hy.1, hy.2, hfail⟩, rfl⟩

/-- **A licensed change admits no valid challenge on the protected fragment.** -/
theorem licensed_no_challenge (V : VocabularyChange A d d') (h : Licensed V)
    (c : Challenge d d') : ¬ c.Valid V V.fragment := by
  intro hc
  obtain ⟨hf, hno⟩ := Challenge.sound hc
  exact hno ((licensed_iff_refines V).1 h c.row hf)

/-- **An unlicensed change admits a valid challenge on the protected fragment.** -/
theorem unlicensed_has_challenge (V : VocabularyChange A d d') (h : ¬ Licensed V) :
    ∃ c : Challenge d d', c.Valid V V.fragment := by
  rw [licensed_iff_refines] at h
  obtain ⟨r, hr⟩ := not_forall.1 h
  obtain ⟨hr, hno⟩ := Classical.not_imp.1 hr
  obtain ⟨c, hc, -⟩ := challenge_complete V V.fragment r ⟨hr, hno⟩
  exact ⟨c, hc⟩

/-- **Adding nothing, certified**, for a change that adds the one coordinate `k`: the new
bundle commits to nothing new on the old coordinates iff every row its elimination leaves has
an entailment certificate against the old commitments. -/
theorem addsNothing_certified {Q : Type*} (k : Fin (d + 1)) (Γ : List (Row d))
    (B' : Bundle Q (d + 1)) :
    AddsNothing (Translation.ofMap k.succAbove) (regionOf Γ) B'.Region ↔
      ∀ c ∈ forget k B', CertEntails Γ c.row := by
  rw [addsNothing_iff, image_ofMap]
  simp only [certEntails_iff_sem, semEntails_iff_forces_regionOf]
  constructor
  · intro h c hc x hx
    exact ((forget_region k B' x).2 (h x hx)).2 c hc
  · intro h x hx
    exact (forget_region k B' x).1 ⟨hx.1, fun c hc => h c hc x hx⟩

/-! ### The split fixture as an occurrence -/

/-- The credence rows of the old vocabulary `(S, ¬S)`. -/
def normRows : List (Row 2) := [⟨![1, 1], 1⟩, ⟨![-1, -1], -1⟩]

/-- The split change with `P(S₁) ≥ 1/5`, `P(S₂) ≥ 1/5`, protecting a declared fragment. -/
def splitChange (fragment : List (Row 2)) : VocabularyChange Unit 2 3 :=
  ⟨(), split.toTranslation, oldB.map CitedRow.row, (newB (1/5) (1/5)).map CitedRow.row, fragment⟩

/-- **Protecting the credence rows alone, the split change is licensed.** -/
theorem split_licensed : Licensed (splitChange normRows) := by
  rw [licensed_iff_refines]
  intro r hr y hy
  refine (pull_sat_iff _ r y).2 (hr _ ?_)
  have hy' := (newB_region _ _ y).1 ((regionOf_bundle _ y).1 hy)
  obtain ⟨hc, h1, -, -⟩ := hy'
  have hpush : (splitChange normRows).T.apply y = ![y 0 + y 1, y 2] := split_push y
  rw [hpush]
  refine ⟨fun i => ?_, fun p hp => ?_⟩
  · fin_cases i
    · exact ⟨by simpa using add_nonneg (hc 0).1 (hc 1).1, by simpa using (by linarith [(hc 2).1] : y 0 + y 1 ≤ 1)⟩
    · simpa using hc 2
  · simp only [splitChange, normRows, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · simp [Row.Sat, Fin.sum_univ_two]; linarith
    · simp [Row.Sat, Fin.sum_univ_two]; linarith

/-- The challenge to the split change on `P(S) ≥ 1/2`: the row itself as its certificate, and
the new credence `(1/5, 1/5, 3/5)`. -/
def splitChallenge : Challenge 2 3 where
  row := atLeast (1/2)
  m := 1
  cert := ⟨fun _ => 1, fun _ => atLeast (1/2), fun _ => by norm_num, fun j => by simp, by simp⟩
  point := ![1/5, 1/5, 3/5]

/-- **The challenge is valid against the old commitments**, and by `licensed_no_challenge` not
against the protected credence rows. -/
theorem splitChallenge_valid :
    splitChallenge.Valid (splitChange normRows) (oldB.map CitedRow.row) ∧
      ¬ splitChallenge.Valid (splitChange normRows) normRows :=
  ⟨by decide +kernel, licensed_no_challenge _ split_licensed _⟩

/-! ## 2. Three readings of a broken commitment -/

section Readings

variable {n n' : ℕ}

/-- A row with its constant relaxed by `s`. -/
def relax {m : ℕ} (r : Row m) (s : ℚ) : Row m := ⟨r.a, r.b + s⟩

theorem relax_sat {m : ℕ} (r : Row m) (s : ℚ) (x : Fin m → ℚ) :
    (relax r s).Sat x ↔ excess r x ≤ s := by
  unfold relax Row.Sat excess
  constructor <;> intro h <;> linarith

/-- **Reading 1 — bars**: the change is admitted only if every listed commitment is kept. -/
def Bars (K : Recollection n n') (C : List (Row n)) (R' : (Fin n' → ℚ) → Prop) : Prop :=
  ∀ r ∈ C, Forces R' (K.pull r)

/-- **Reading 2 — accounted**: the change is admitted with each listed commitment relaxed by
its nonnegative charge `s r`. -/
def Accounted (K : Recollection n n') (C : List (Row n)) (R' : (Fin n' → ℚ) → Prop)
    (s : Row n → ℚ) : Prop :=
  ∀ r ∈ C, 0 ≤ s r ∧ Forces R' (relax (K.pull r) (s r))

/-- **Reading 3 — the split**: a listed commitment whose obligation is live must be kept; any
other is relaxed by its charge. -/
def Split (K : Recollection n n') (C : List (Row n)) (R' : (Fin n' → ℚ) → Prop)
    (live : Row n → Prop) (s : Row n → ℚ) : Prop :=
  ∀ r ∈ C, (live r → Forces R' (K.pull r)) ∧ 0 ≤ s r ∧ Forces R' (relax (K.pull r) (s r))

/-- Bars is the accounted reading at charge zero. -/
theorem bars_iff_accounted_zero (K : Recollection n n') (C : List (Row n))
    (R' : (Fin n' → ℚ) → Prop) : Bars K C R' ↔ Accounted K C R' fun _ => 0 := by
  unfold Bars Accounted Forces
  simp only [le_refl, true_and, relax_sat, ← sat_iff_excess]

/-- With no live commitment the split is the accounted reading. -/
theorem split_none_live (K : Recollection n n') (C : List (Row n)) (R' : (Fin n' → ℚ) → Prop)
    (live : Row n → Prop) (s : Row n → ℚ) (h : ∀ r ∈ C, ¬ live r) :
    Split K C R' live s ↔ Accounted K C R' s :=
  ⟨fun hs r hr => (hs r hr).2, fun ha r hr => ⟨fun hl => absurd hl (h r hr), ha r hr⟩⟩

/-- With every commitment live the split is the bars reading, at any nonnegative charges. -/
theorem split_all_live (K : Recollection n n') (C : List (Row n)) (R' : (Fin n' → ℚ) → Prop)
    (live : Row n → Prop) (s : Row n → ℚ) (h : ∀ r ∈ C, live r) :
    Split K C R' live s ↔ Bars K C R' ∧ ∀ r ∈ C, 0 ≤ s r := by
  constructor
  · exact fun hs => ⟨fun r hr => (hs r hr).1 (h r hr), fun r hr => (hs r hr).2.1⟩
  · rintro ⟨hb, h0⟩ r hr
    refine ⟨fun _ => hb r hr, h0 r hr, fun q hq => ?_⟩
    have := (sat_iff_excess _ _).1 (hb r hr q hq)
    exact (relax_sat _ _ _).2 (this.trans (h0 r hr))

/-- **The charge** of a commitment: the largest excess of its pullback over the new region,
attained. -/
def Charge (K : Recollection n n') (R' : (Fin n' → ℚ) → Prop) (r : Row n) (s : ℚ) : Prop :=
  (∀ q, R' q → excess r (K.push q) ≤ s) ∧ ∃ q, R' q ∧ excess r (K.push q) = s

theorem forces_relax_iff {K : Recollection n n'} {R' : (Fin n' → ℚ) → Prop} {r : Row n} {s : ℚ}
    (h : Charge K R' r s) (t : ℚ) : Forces R' (relax (K.pull r) t) ↔ s ≤ t := by
  unfold Forces
  simp only [relax_sat, excess_pull]
  constructor
  · intro hf
    obtain ⟨q, hq, he⟩ := h.2
    rw [← he]
    exact hf q hq
  · exact fun hst q hq => (h.1 q hq).trans hst

theorem forces_pull_iff {K : Recollection n n'} {R' : (Fin n' → ℚ) → Prop} {r : Row n} {s : ℚ}
    (h : Charge K R' r s) : Forces R' (K.pull r) ↔ s ≤ 0 := by
  rw [← forces_relax_iff h 0]
  unfold Forces
  simp only [relax_sat, ← sat_iff_excess]

/-- **Each reading's verdict on one commitment is a function of its charge.** -/
theorem readings_of_charge {K : Recollection n n'} {R' : (Fin n' → ℚ) → Prop} {r : Row n}
    {s : ℚ} (h : Charge K R' r s) (live : Row n → Prop) (t : Row n → ℚ) :
    (Bars K [r] R' ↔ s ≤ 0) ∧ (Accounted K [r] R' t ↔ 0 ≤ t r ∧ s ≤ t r) ∧
      (Split K [r] R' live t ↔ (live r → s ≤ 0) ∧ 0 ≤ t r ∧ s ≤ t r) := by
  unfold Bars Accounted Split
  simp only [List.mem_singleton, forall_eq, forces_pull_iff h, forces_relax_iff h, and_self]

/-- A commitment of positive charge: bars refuses; accounted admits at that charge; the split
refuses if it is live and admits at that charge if it is not. -/
theorem readings_of_pos_charge {K : Recollection n n'} {R' : (Fin n' → ℚ) → Prop} {r : Row n}
    {s : ℚ} (h : Charge K R' r s) (hs : 0 < s) :
    ¬ Bars K [r] R' ∧ Accounted K [r] R' (fun _ => s) ∧
      (∀ live t, live r → ¬ Split K [r] R' live t) ∧
      ∀ live : Row n → Prop, ¬ live r → Split K [r] R' live fun _ => s := by
  refine ⟨fun hb => ?_, ?_, fun live t hl hsp => ?_, fun live hl => ?_⟩
  · exact absurd ((readings_of_charge h (fun _ => False) fun _ => 0).1.1 hb) (not_le.2 hs)
  · exact (readings_of_charge h (fun _ => False) _).2.1.2 ⟨hs.le, le_rfl⟩
  · exact absurd (((readings_of_charge h live t).2.2.1 hsp).1 hl) (not_le.2 hs)
  · exact (readings_of_charge h live _).2.2.2 ⟨fun hl' => absurd hl' hl, hs.le, le_rfl⟩

/-- A commitment of charge zero: every reading admits the change at no charge, live or not. -/
theorem readings_of_zero_charge {K : Recollection n n'} {R' : (Fin n' → ℚ) → Prop} {r : Row n}
    (h : Charge K R' r 0) :
    Bars K [r] R' ∧ Accounted K [r] R' (fun _ => 0) ∧
      ∀ live : Row n → Prop, Split K [r] R' live fun _ => 0 :=
  ⟨(readings_of_charge h (fun _ => False) fun _ => 0).1.2 le_rfl,
    (readings_of_charge h (fun _ => False) _).2.1.2 ⟨le_rfl, le_rfl⟩,
    fun live => (readings_of_charge h live _).2.2.2 ⟨fun _ => le_rfl, le_rfl, le_rfl⟩⟩

end Readings

/-! ### Charges on the fixtures -/

/-- **The split fixture**: `P(S) ≥ 1/2` against `P(S₁) ≥ 1/5`, `P(S₂) ≥ 1/5` is charged
`1/10`. -/
theorem split_charge : Charge split (newB (1/5) (1/5)).Region (atLeast (1/2)) (1/10) := by
  refine ⟨fun q hq => ?_, ![1/5, 1/5, 3/5], by decide +kernel, ?_⟩
  · obtain ⟨-, -, h0, h1⟩ := (newB_region _ _ q).1 hq
    rw [split_push]
    simp only [excess, atLeast, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith
  · rw [split_push]
    simp [excess, atLeast, Fin.sum_univ_two]
    norm_num

/-- The credences over two worlds. -/
def simplex2 (q : Fin 2 → ℚ) : Prop := (∀ w, 0 ≤ q w) ∧ q 0 + q 1 = 1

lemma simplex2_left : simplex2 ![1, 0] := ⟨fun w => by fin_cases w <;> simp, by simp⟩

lemma simplex2_right : simplex2 ![0, 1] := ⟨fun w => by fin_cases w <;> simp, by simp⟩

/-- **Abandonment**: `P(S) ≥ 9/10` is charged `13/20`, and at least `3/20` at every new
credence. -/
theorem abandon_charge :
    Charge abandon simplex2 (atLeast (9/10)) (13/20) ∧
      ∀ q, simplex2 q → 3/20 ≤ excess (atLeast (9/10)) (abandon.push q) := by
  have hex : ∀ q : Fin 2 → ℚ,
      excess (atLeast (9/10)) (abandon.push q) = 9/10 - (1/4 * q 0 + 3/4 * q 1) := by
    intro q
    rw [abandon_push]
    simp only [excess, atLeast, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  refine ⟨⟨fun q hq => ?_, ![1, 0], simplex2_left, ?_⟩, fun q hq => ?_⟩
  · rw [hex]; linarith [hq.1 0, hq.1 1, hq.2]
  · rw [hex]; simp; norm_num
  · rw [hex]; linarith [hq.1 0, hq.1 1, hq.2]

/-- The commitment `P(X∧Y) ≥ 3/4 · P(X)` over the worlds `(X∧Y, X∧¬Y, ¬X∧Y, ¬X∧¬Y)`. -/
def liveRow : Row 4 := ⟨![-1/4, 3/4, 0, 0], 0⟩

/-- The pin `P(X) ≥ 1`: what the record gains when `X` settles true. -/
def pinX : Row 4 := ⟨![-1, -1, 0, 0], -1⟩

/-- Dropping `X`, retold as a fair coin independent of `Y`: new worlds `(Y, ¬Y)`. -/
def halfK : Recollection 4 2 where
  k := ![![1/2, 0, 1/2, 0], ![0, 1/2, 0, 1/2]]
  nonneg w' w := by fin_cases w' <;> fin_cases w <;> norm_num
  sum_one w' := by fin_cases w' <;> simp [Fin.sum_univ_four] <;> norm_num

/-- Dropping `X`, retold as false. -/
def zeroK : Recollection 4 2 := Recollection.ofMap ![2, 3]

theorem halfK_push (q : Fin 2 → ℚ) :
    halfK.push q = ![1/2 * q 0, 1/2 * q 1, 1/2 * q 0, 1/2 * q 1] := by
  funext w
  fin_cases w <;>
    simp [halfK, Recollection.push, Translation.apply, Recollection.toTranslation,
      Fin.sum_univ_two]

theorem zeroK_push (q : Fin 2 → ℚ) : zeroK.push q = ![0, 0, q 0, q 1] := by
  funext w
  fin_cases w <;>
    simp [zeroK, Recollection.push, Translation.apply, Recollection.toTranslation,
      Recollection.ofMap, Fin.sum_univ_two]

lemma excess_liveRow (p : Fin 4 → ℚ) : excess liveRow p = -1/4 * p 0 + 3/4 * p 1 := by
  simp [excess, liveRow, Fin.sum_univ_four]

lemma excess_pinX (p : Fin 4 → ℚ) : excess pinX p = 1 - p 0 - p 1 := by
  simp [excess, pinX, Fin.sum_univ_four]
  ring

/-- **The live commitment, `X` retold as a fair coin**: charged `3/8`. -/
theorem half_charge : Charge halfK simplex2 liveRow (3/8) := by
  refine ⟨fun q hq => ?_, ![0, 1], simplex2_right, ?_⟩
  · rw [excess_liveRow, halfK_push]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith [hq.1 0, hq.1 1, hq.2]
  · rw [excess_liveRow, halfK_push]
    simp
    norm_num

/-- **The live commitment, `X` retold as false**: charged `0`. -/
theorem zero_charge : Charge zeroK simplex2 liveRow 0 := by
  refine ⟨fun q _ => ?_, ![1, 0], simplex2_left, ?_⟩
  · rw [excess_liveRow, zeroK_push]; simp
  · rw [excess_liveRow, zeroK_push]; simp

/-- **Every reading admits the change that retells `X` as false, at no charge**, whether or
not the commitment's obligation is live. -/
theorem zero_admitted :
    Bars zeroK [liveRow] simplex2 ∧ Accounted zeroK [liveRow] simplex2 (fun _ => 0) ∧
      ∀ live : Row 4 → Prop, Split zeroK [liveRow] simplex2 live fun _ => 0 :=
  readings_of_zero_charge zero_charge

/-- **After `X` settles true**, the pin `P(X) ≥ 1` under the fair-coin retelling: charged
`1/2`, at every new credence. -/
theorem half_pin_charge :
    Charge halfK simplex2 pinX (1/2) ∧ ∀ q, simplex2 q → excess pinX (halfK.push q) = 1/2 := by
  have hex : ∀ q, simplex2 q → excess pinX (halfK.push q) = 1/2 := by
    intro q hq
    rw [excess_pinX, halfK_push]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith [hq.2]
  exact ⟨⟨fun q hq => (hex q hq).le, ![1, 0], simplex2_left, hex _ simplex2_left⟩, hex⟩

/-- **After `X` settles true**, the pin under the retelling of `X` as false: charged `1`, at
every new credence. -/
theorem zero_pin_charge :
    Charge zeroK simplex2 pinX 1 ∧ ∀ q, simplex2 q → excess pinX (zeroK.push q) = 1 := by
  have hex : ∀ q, excess pinX (zeroK.push q) = 1 := by
    intro q
    rw [excess_pinX, zeroK_push]
    simp
  exact ⟨⟨fun q _ => (hex q).le, ![1, 0], simplex2_left, hex _⟩, fun q _ => hex q⟩

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.VocabularyAct.regionOf
#print axioms Workspace.Normativity.Contrib.VocabularyAct.semEntails_iff_forces_regionOf
#print axioms Workspace.Normativity.Contrib.VocabularyAct.regionOf_bundle
#print axioms Workspace.Normativity.Contrib.VocabularyAct.BrokenAlong
#print axioms Workspace.Normativity.Contrib.VocabularyAct.broken_iff_brokenAlong
#print axioms Workspace.Normativity.Contrib.VocabularyAct.VocabularyChange
#print axioms Workspace.Normativity.Contrib.VocabularyAct.Licensed
#print axioms Workspace.Normativity.Contrib.VocabularyAct.licensed_iff_refines
#print axioms Workspace.Normativity.Contrib.VocabularyAct.Challenge
#print axioms Workspace.Normativity.Contrib.VocabularyAct.Challenge.Valid
#print axioms Workspace.Normativity.Contrib.VocabularyAct.Challenge.sound
#print axioms Workspace.Normativity.Contrib.VocabularyAct.challenge_complete
#print axioms Workspace.Normativity.Contrib.VocabularyAct.licensed_no_challenge
#print axioms Workspace.Normativity.Contrib.VocabularyAct.unlicensed_has_challenge
#print axioms Workspace.Normativity.Contrib.VocabularyAct.addsNothing_certified
#print axioms Workspace.Normativity.Contrib.VocabularyAct.normRows
#print axioms Workspace.Normativity.Contrib.VocabularyAct.splitChange
#print axioms Workspace.Normativity.Contrib.VocabularyAct.split_licensed
#print axioms Workspace.Normativity.Contrib.VocabularyAct.splitChallenge
#print axioms Workspace.Normativity.Contrib.VocabularyAct.splitChallenge_valid
#print axioms Workspace.Normativity.Contrib.VocabularyAct.relax
#print axioms Workspace.Normativity.Contrib.VocabularyAct.relax_sat
#print axioms Workspace.Normativity.Contrib.VocabularyAct.Bars
#print axioms Workspace.Normativity.Contrib.VocabularyAct.Accounted
#print axioms Workspace.Normativity.Contrib.VocabularyAct.Split
#print axioms Workspace.Normativity.Contrib.VocabularyAct.bars_iff_accounted_zero
#print axioms Workspace.Normativity.Contrib.VocabularyAct.split_none_live
#print axioms Workspace.Normativity.Contrib.VocabularyAct.split_all_live
#print axioms Workspace.Normativity.Contrib.VocabularyAct.Charge
#print axioms Workspace.Normativity.Contrib.VocabularyAct.forces_relax_iff
#print axioms Workspace.Normativity.Contrib.VocabularyAct.forces_pull_iff
#print axioms Workspace.Normativity.Contrib.VocabularyAct.readings_of_charge
#print axioms Workspace.Normativity.Contrib.VocabularyAct.readings_of_pos_charge
#print axioms Workspace.Normativity.Contrib.VocabularyAct.readings_of_zero_charge
#print axioms Workspace.Normativity.Contrib.VocabularyAct.split_charge
#print axioms Workspace.Normativity.Contrib.VocabularyAct.simplex2
#print axioms Workspace.Normativity.Contrib.VocabularyAct.simplex2_left
#print axioms Workspace.Normativity.Contrib.VocabularyAct.simplex2_right
#print axioms Workspace.Normativity.Contrib.VocabularyAct.abandon_charge
#print axioms Workspace.Normativity.Contrib.VocabularyAct.liveRow
#print axioms Workspace.Normativity.Contrib.VocabularyAct.pinX
#print axioms Workspace.Normativity.Contrib.VocabularyAct.halfK
#print axioms Workspace.Normativity.Contrib.VocabularyAct.zeroK
#print axioms Workspace.Normativity.Contrib.VocabularyAct.halfK_push
#print axioms Workspace.Normativity.Contrib.VocabularyAct.zeroK_push
#print axioms Workspace.Normativity.Contrib.VocabularyAct.excess_liveRow
#print axioms Workspace.Normativity.Contrib.VocabularyAct.excess_pinX
#print axioms Workspace.Normativity.Contrib.VocabularyAct.half_charge
#print axioms Workspace.Normativity.Contrib.VocabularyAct.zero_charge
#print axioms Workspace.Normativity.Contrib.VocabularyAct.zero_admitted
#print axioms Workspace.Normativity.Contrib.VocabularyAct.half_pin_charge
#print axioms Workspace.Normativity.Contrib.VocabularyAct.zero_pin_charge

end Workspace.Normativity.Contrib.VocabularyAct
