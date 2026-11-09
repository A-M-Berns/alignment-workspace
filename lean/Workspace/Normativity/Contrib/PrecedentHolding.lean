/-
# The holding of a case base: what permission reads, and what may be forgotten

Round `projects/normativity/rounds/2026-11-08-content-recollection/`, follow-up of 2026-11-09,
matter 1.

`PrecedentConstraint.Permitted Γ c` is rationalizability of `c :: Γ`.  The **holding** of a
case base (`Holding`) is the transitive closure of its dominance relation on reason sets, and
its **reach** (`Reach`) is the holding together with `Covers`.

§1.  The holding of `c :: Γ` is computed from the holding of `Γ` and `c` (`holding_cons`), and
a continuation is permitted iff the base is rationalizable and its reach does not put the
continuation's losers at or above its winners (`permitted_iff`).  So two case bases with the
same holding permit the same continuations, now and after any further continuations
(`permitted_congr`, `holding_append_congr`): the cases may be forgotten and the holding kept.
Among rationalizable bases the reach is exactly what permission reads
(`permission_eq_iff_reach_eq`); the holding is finer than that — a case whose winners cover
its losers enters the holding and leaves the reach unchanged (`reach_cons_of_covers`,
`holding_not_minimal`).

§2.  Size.  Restricted to a set `R` of reason sets containing the winners and losers of every
continuation, the reach on `R × R` with the rationalizability bit is closed under
continuation (`agreeOn_cons`).  For finite `R` it is a subset of `R × R`, it only grows
(`reach_mono`), and along any sequence of continuations it is eventually constant
(`reachSet_eventually_const`, by `SeedStatics.eventually_const_of_finite`), after which
permission over `R` is constant (`permission_eventually_const`).  Without a finite set of
strengths no such bound holds: over one pair of kinds, `n` cases at `n` strengths are each
needed (`staircase_irredundant`), at strengths inside `(0,1)` (`humbleScale`).

§3.  Merging.  The union of two case bases is rationalizable iff the union of their holdings
has no cycle (`rationalizable_append_iff`).  Two rationalizable bases whose union is not:
directly (`merged_discord`), and with every pair of cases compatible
(`merged_discord_hidden`).

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.PrecedentConstraint

namespace Workspace.Normativity.Contrib.PrecedentHolding

open Workspace.Normativity.Contrib.SeedStatics
open Workspace.Normativity.Contrib.WarrantEntitlement
open Workspace.Normativity.Contrib.PrecedentConstraint

variable {d : ℕ}

/-! ## 1. The holding, the reach, and what permission reads -/

theorem dominates_cons (c : Case d) (Γ : List (Case d)) (V U : List (Form d)) :
    Dominates (c :: Γ) V U ↔ Beats c V U ∨ Dominates Γ V U := by
  constructor
  · rintro ⟨c', hc', hb⟩
    rcases List.mem_cons.1 hc' with rfl | h
    · exact Or.inl hb
    · exact Or.inr ⟨c', h, hb⟩
  · rintro (hb | ⟨c', h, hb⟩)
    · exact ⟨c, List.mem_cons_self, hb⟩
    · exact ⟨c', List.mem_cons_of_mem _ h, hb⟩

theorem Dominates.covers_left {Γ : List (Case d)} {V V' U : List (Form d)} (h : Dominates Γ V U)
    (hc : Covers V' V) : Dominates Γ V' U := by
  obtain ⟨c, hc', hV, hU⟩ := h
  exact ⟨c, hc', hc.trans hV, hU⟩

theorem Dominates.covers_right {Γ : List (Case d)} {V U U' : List (Form d)} (h : Dominates Γ V U)
    (hc : Covers U U') : Dominates Γ V U' := by
  obtain ⟨c, hc', hV, hU⟩ := h
  exact ⟨c, hc', hV, hU.trans hc⟩

/-- **The holding** of a case base: the transitive closure of dominance on reason sets. -/
def Holding (Γ : List (Case d)) : List (Form d) → List (Form d) → Prop :=
  Relation.TransGen (Dominates Γ)

theorem Holding.trans {Γ : List (Case d)} {U V W : List (Form d)} (h₁ : Holding Γ U V)
    (h₂ : Holding Γ V W) : Holding Γ U W :=
  Relation.TransGen.trans h₁ h₂

theorem Holding.covers_left {Γ : List (Case d)} {V V' U : List (Form d)} (h : Holding Γ V U)
    (hc : Covers V' V) : Holding Γ V' U := by
  obtain ⟨M, hVM, hMU⟩ := Relation.TransGen.head'_iff.1 h
  exact Relation.TransGen.head' (Dominates.covers_left hVM hc) hMU

theorem Holding.covers_right {Γ : List (Case d)} {V U U' : List (Form d)} (h : Holding Γ V U)
    (hc : Covers U U') : Holding Γ V U' := by
  obtain ⟨M, hVM, hMU⟩ := Relation.TransGen.tail'_iff.1 h
  exact Relation.TransGen.tail' hVM (Dominates.covers_right hMU hc)

/-- A case base is rationalizable iff its holding is irreflexive. -/
theorem rationalizable_iff_holding (Γ : List (Case d)) :
    Rationalizable Γ ↔ ∀ U, ¬ Holding Γ U U :=
  rationalizable_iff_no_dominance_cycle Γ

/-- **The holding only grows** with the case base. -/
theorem holding_mono {Γ Γ' : List (Case d)} (h : ∀ c ∈ Γ, c ∈ Γ') {V U : List (Form d)}
    (hh : Holding Γ V U) : Holding Γ' V U :=
  Relation.TransGen.mono (fun _ _ ⟨c, hc, hb⟩ => ⟨c, h c hc, hb⟩) hh

/-- **The reach** of a case base: one reason set is at or above another when it covers it or
the holding puts it above. -/
def Reach (Γ : List (Case d)) (V U : List (Form d)) : Prop := Covers V U ∨ Holding Γ V U

theorem Reach.refl (Γ : List (Case d)) (V : List (Form d)) : Reach Γ V V := Or.inl (Covers.refl V)

theorem Reach.trans {Γ : List (Case d)} {U V W : List (Form d)} (h₁ : Reach Γ U V)
    (h₂ : Reach Γ V W) : Reach Γ U W := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact Or.inl (h₁.trans h₂)
  · exact Or.inr (h₂.covers_left h₁)
  · exact Or.inr (h₁.covers_right h₂)
  · exact Or.inr (h₁.trans h₂)

/-- **The holding after a continuation**, from the holding before it and the case alone. -/
theorem holding_cons (c : Case d) (Γ : List (Case d)) (V U : List (Form d)) :
    Holding (c :: Γ) V U ↔ Holding Γ V U ∨ (Reach Γ V c.winners ∧ Reach Γ c.losers U) := by
  constructor
  · intro h
    have h' : Relation.TransGen (Dominates (c :: Γ)) V U := h
    induction h' with
    | single hd =>
      rcases (dominates_cons c Γ _ _).1 hd with hb | hd
      · exact Or.inr ⟨Or.inl hb.1, Or.inl hb.2⟩
      · exact Or.inl (Relation.TransGen.single hd)
    | tail hprev hd ih =>
      have ih := ih hprev
      rcases (dominates_cons c Γ _ _).1 hd with hb | hd
      · refine Or.inr ⟨?_, Or.inl hb.2⟩
        rcases ih with ih | ih
        · exact Or.inr (ih.covers_right hb.1)
        · exact ih.1
      · rcases ih with ih | ih
        · exact Or.inl (Relation.TransGen.tail ih hd)
        · exact Or.inr ⟨ih.1, ih.2.trans (Or.inr (Relation.TransGen.single hd))⟩
  · rintro (h | ⟨hV, hU⟩)
    · exact holding_mono (fun c' hc' => List.mem_cons_of_mem _ hc') h
    · have hΓ : ∀ c' ∈ Γ, c' ∈ c :: Γ := fun c' hc' => List.mem_cons_of_mem _ hc'
      have step : Holding (c :: Γ) c.winners c.losers :=
        Relation.TransGen.single ⟨c, List.mem_cons_self, Covers.refl _, Covers.refl _⟩
      have h1 : Holding (c :: Γ) V c.losers := by
        rcases hV with hV | hV
        · exact step.covers_left hV
        · exact (holding_mono hΓ hV).trans step
      rcases hU with hU | hU
      · exact h1.covers_right hU
      · exact h1.trans (holding_mono hΓ hU)

/-- The reach after a continuation, from the reach before it and the case alone. -/
theorem reach_cons (c : Case d) (Γ : List (Case d)) (V U : List (Form d)) :
    Reach (c :: Γ) V U ↔ Reach Γ V U ∨ (Reach Γ V c.winners ∧ Reach Γ c.losers U) := by
  show Covers V U ∨ Holding (c :: Γ) V U ↔ (Covers V U ∨ Holding Γ V U) ∨ _
  rw [holding_cons, or_assoc]

/-- **The reach only grows** under a continuation. -/
theorem reach_mono (c : Case d) (Γ : List (Case d)) {V U : List (Form d)} (h : Reach Γ V U) :
    Reach (c :: Γ) V U :=
  (reach_cons c Γ V U).2 (Or.inl h)

/-- **What permission reads.**  A continuation is permitted iff the base is rationalizable and
its reach does not put the continuation's losers at or above its winners. -/
theorem permitted_iff (Γ : List (Case d)) (c : Case d) :
    Permitted Γ c ↔ Rationalizable Γ ∧ ¬ Reach Γ c.losers c.winners := by
  unfold Permitted
  rw [rationalizable_iff_holding, rationalizable_iff_holding]
  constructor
  · intro h
    refine ⟨fun U hU => h U ((holding_cons c Γ U U).2 (Or.inl hU)), fun hr => ?_⟩
    exact h c.winners ((holding_cons c Γ _ _).2 (Or.inr ⟨Reach.refl Γ _, hr⟩))
  · rintro ⟨hΓ, hr⟩ U hU
    rcases (holding_cons c Γ U U).1 hU with h | ⟨h₁, h₂⟩
    · exact hΓ U h
    · exact hr (h₂.trans h₁)

/-- **The holding is a sufficient statistic for permission**: two case bases with the same
holding permit exactly the same continuations. -/
theorem permitted_congr {Γ Γ' : List (Case d)} (h : ∀ V U, Holding Γ V U ↔ Holding Γ' V U)
    (c : Case d) : Permitted Γ c ↔ Permitted Γ' c := by
  rw [permitted_iff, permitted_iff, rationalizable_iff_holding, rationalizable_iff_holding]
  unfold Reach
  simp only [h]

/-- Two case bases with the same holding have the same holding after any continuations. -/
theorem holding_append_congr {Γ Γ' : List (Case d)} (h : ∀ V U, Holding Γ V U ↔ Holding Γ' V U)
    (cs : List (Case d)) : ∀ V U, Holding (cs ++ Γ) V U ↔ Holding (cs ++ Γ') V U := by
  induction cs with
  | nil => exact h
  | cons c cs ih =>
    intro V U
    rw [List.cons_append, List.cons_append, holding_cons, holding_cons]
    unfold Reach
    simp only [ih]

/-- **The cases may be forgotten and the holding kept**: two case bases with the same holding
permit the same continuations after any further continuations. -/
theorem permitted_append_congr {Γ Γ' : List (Case d)}
    (h : ∀ V U, Holding Γ V U ↔ Holding Γ' V U) (cs : List (Case d)) (c : Case d) :
    Permitted (cs ++ Γ) c ↔ Permitted (cs ++ Γ') c :=
  permitted_congr (holding_append_congr h cs) c

/-- **Among rationalizable case bases the reach is exactly what permission reads**: two of them
permit the same continuations iff they have the same reach. -/
theorem permission_eq_iff_reach_eq {Γ Γ' : List (Case d)} (hΓ : Rationalizable Γ)
    (hΓ' : Rationalizable Γ') :
    (∀ c, Permitted Γ c ↔ Permitted Γ' c) ↔ ∀ V U, Reach Γ V U ↔ Reach Γ' V U := by
  constructor
  · intro h V U
    have := h ⟨U, V⟩
    rw [permitted_iff, permitted_iff] at this
    simp only [hΓ, hΓ', true_and] at this
    exact not_iff_not.1 this
  · intro h c
    rw [permitted_iff, permitted_iff]
    simp only [hΓ, hΓ', true_and, h]

/-- A case whose winners cover its losers leaves the reach unchanged. -/
theorem reach_cons_of_covers (c : Case d) (Γ : List (Case d)) (hc : Covers c.winners c.losers)
    (V U : List (Form d)) : Reach (c :: Γ) V U ↔ Reach Γ V U := by
  rw [reach_cons]
  constructor
  · rintro (h | ⟨h₁, h₂⟩)
    · exact h
    · exact h₁.trans (Reach.trans (Or.inl hc) h₂)
  · exact Or.inl

theorem holding_nil (V U : List (Form d)) : ¬ Holding ([] : List (Case d)) V U := by
  intro h
  obtain ⟨M, ⟨c, hc, -⟩, -⟩ := Relation.TransGen.head'_iff.1 h
  exact absurd hc List.not_mem_nil

/-- A case over `(X, Y)` whose winners `P(X) ≥ 1, P(Y) ≥ 1` cover its loser `P(Y) ≥ 1/2`. -/
def vacuous : Case 2 := ⟨[Form.premise 0 1, Form.premise 1 1], [Form.premise 1 (1/2)]⟩

/-- **The holding is finer than what permission reads**: the base `[vacuous]` and the empty
base have the same reach, so they permit the same continuations, and different holdings. -/
theorem holding_not_minimal :
    (∀ V U, Reach [vacuous] V U ↔ Reach ([] : List (Case 2)) V U) ∧
      (∀ c, Permitted [vacuous] c ↔ Permitted ([] : List (Case 2)) c) ∧
      Holding [vacuous] vacuous.winners vacuous.losers ∧
      ¬ Holding ([] : List (Case 2)) vacuous.winners vacuous.losers := by
  have hreach : ∀ V U, Reach [vacuous] V U ↔ Reach ([] : List (Case 2)) V U :=
    reach_cons_of_covers vacuous [] (by decide +kernel)
  have hnil : Rationalizable ([] : List (Case 2)) :=
    (rationalizable_iff_holding _).2 fun U => holding_nil U U
  have hvac : Rationalizable [vacuous] := rationalizable_of_rank (fun _ => 0) (by decide +kernel)
  exact ⟨hreach, (permission_eq_iff_reach_eq hvac hnil).2 hreach,
    Relation.TransGen.single ⟨vacuous, List.mem_cons_self, Covers.refl _, Covers.refl _⟩,
    holding_nil _ _⟩

/-! ## 2. Size: a finite universe of reason sets, and the staircase -/

/-- Two case bases **agree on** a set of reason sets: both rationalizable or neither, and the
same reach between members of the set. -/
def AgreeOn (R : Set (List (Form d))) (Γ Γ' : List (Case d)) : Prop :=
  (Rationalizable Γ ↔ Rationalizable Γ') ∧ ∀ V ∈ R, ∀ U ∈ R, Reach Γ V U ↔ Reach Γ' V U

/-- **The restricted reach is closed under continuation**: two case bases that agree on `R`
permit the same continuations with winners and losers in `R`, and agree on `R` after one. -/
theorem agreeOn_cons {R : Set (List (Form d))} {Γ Γ' : List (Case d)} (h : AgreeOn R Γ Γ')
    {c : Case d} (hw : c.winners ∈ R) (hl : c.losers ∈ R) :
    (Permitted Γ c ↔ Permitted Γ' c) ∧ AgreeOn R (c :: Γ) (c :: Γ') := by
  have hperm : Permitted Γ c ↔ Permitted Γ' c := by
    rw [permitted_iff, permitted_iff, h.1, h.2 _ hl _ hw]
  refine ⟨hperm, hperm, fun V hV U hU => ?_⟩
  rw [reach_cons, reach_cons, h.2 V hV U hU, h.2 V hV _ hw, h.2 _ hl U hU]

open Classical in
/-- The reach restricted to a finite universe `R` of reason sets, as a subset of `R × R`. -/
noncomputable def reachSet (R : Finset (List (Form d))) (Γ : List (Case d)) :
    Finset {p : List (Form d) × List (Form d) // p ∈ R ×ˢ R} :=
  Finset.univ.filter fun p => Reach Γ p.1.1 p.1.2

theorem mem_reachSet {R : Finset (List (Form d))} {Γ : List (Case d)}
    (p : {p : List (Form d) × List (Form d) // p ∈ R ×ˢ R}) :
    p ∈ reachSet R Γ ↔ Reach Γ p.1.1 p.1.2 := by
  simp [reachSet]

/-- **Over a finite universe of reason sets the reach is eventually constant** along any
sequence of continuations. -/
theorem reachSet_eventually_const (R : Finset (List (Form d))) (Γ : ℕ → List (Case d))
    (c : ℕ → Case d) (hstep : ∀ n, Γ (n + 1) = c n :: Γ n) :
    ∃ N, ∀ n, N ≤ n → reachSet R (Γ n) = reachSet R (Γ N) := by
  have hmono : Monotone fun n => reachSet R (Γ n) := by
    refine monotone_nat_of_le_succ fun n p hp => ?_
    rw [mem_reachSet] at hp ⊢
    rw [hstep]
    exact reach_mono _ _ hp
  exact eventually_const_of_finite (d := 0) (fun n => reachSet R (Γ n)) hmono (fun _ => ∅)
    monotone_const fun A _ => A

/-- **Permission over a finite universe of reason sets is eventually constant** along any
sequence of permitted continuations of a rationalizable base. -/
theorem permission_eventually_const (R : Finset (List (Form d))) (Γ : ℕ → List (Case d))
    (c : ℕ → Case d) (hstep : ∀ n, Γ (n + 1) = c n :: Γ n) (h0 : Rationalizable (Γ 0))
    (hperm : ∀ n, Permitted (Γ n) (c n)) :
    ∃ N, ∀ n, N ≤ n → ∀ c', c'.winners ∈ R → c'.losers ∈ R →
      (Permitted (Γ n) c' ↔ Permitted (Γ N) c') := by
  have hrat : ∀ n, Rationalizable (Γ n) := by
    intro n
    cases n with
    | zero => exact h0
    | succ n => rw [hstep]; exact hperm n
  obtain ⟨N, hN⟩ := reachSet_eventually_const R Γ c hstep
  refine ⟨N, fun n hn c' hw hl => ?_⟩
  have hmem : (c'.losers, c'.winners) ∈ R ×ˢ R := Finset.mem_product.2 ⟨hl, hw⟩
  have key := Finset.ext_iff.1 (hN n hn) ⟨_, hmem⟩
  rw [mem_reachSet, mem_reachSet] at key
  rw [permitted_iff, permitted_iff]
  simp only [hrat, true_and, key]

theorem covers_singleton (v w : Form d) : Covers [v] [w] ↔ kind v = kind w ∧ w.c ≤ v.c := by
  simp [Covers]

/-- `P(X) ≥ s j` prevailed over `P(¬X) ≥ s j`. -/
def step (s : ℕ → ℚ) (j : ℕ) : Case 2 := ⟨[Form.premise 0 (s j)], [Form.premise 1 (s j)]⟩

/-- The reverse decision at strength `s i`. -/
def against (s : ℕ → ℚ) (i : ℕ) : Case 2 := ⟨[Form.premise 1 (s i)], [Form.premise 0 (s i)]⟩

/-- **The staircase**: `n` cases over one pair of kinds, at the strengths `s 0, …, s (n-1)`. -/
def staircase (s : ℕ → ℚ) (n : ℕ) : List (Case 2) := (List.range n).map (step s)

/-- **Every case of the staircase is needed.**  With strictly increasing strengths, the
reverse decision at the `i`-th strength is forbidden by the staircase and permitted by the
staircase without its `i`-th case: no part of the holding over this one pair of kinds is
implied by the rest, whatever `n` is. -/
theorem staircase_irredundant (s : ℕ → ℚ) (hs : StrictMono s) (n i : ℕ) (hi : i < n) :
    ¬ Permitted (staircase s n) (against s i) ∧
      Permitted ((staircase s n).filter fun c => c ≠ step s i) (against s i) := by
  constructor
  · intro h
    exact (consistent_iff_pairwise _).1 h.consistent (against s i) List.mem_cons_self (step s i)
      (List.mem_cons_of_mem _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))
      ⟨Covers.refl _, Covers.refl _⟩
  · have hne : ∀ j, step s j ≠ against s i := by
      intro j h
      have := congrArg Case.winners h
      simp [step, against] at this
    have mem : ∀ x ∈ against s i :: (staircase s n).filter (fun c => c ≠ step s i),
        x = against s i ∨ ∃ j, j ≠ i ∧ x = step s j := by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inl rfl
      · obtain ⟨hx1, hx2⟩ := List.mem_filter.1 hx
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx1
        refine Or.inr ⟨j, ?_, rfl⟩
        rintro rfl
        simp at hx2
    refine rationalizable_of_rank
      (fun c => if c = against s i then 1 else if s i < (c.winners.map Form.c).sum then 0 else 2) ?_
    have rank_step : ∀ j, (if step s j = against s i then 1
        else if s i < ((step s j).winners.map Form.c).sum then 0 else 2) =
          if s i < s j then 0 else (2 : ℕ) := by
      intro j
      rw [if_neg (hne j)]
      simp [step, Form.c]
    intro x hx y hy hcov
    rcases mem x hx with rfl | ⟨j, hj, rfl⟩ <;> rcases mem y hy with rfl | ⟨k, hk, rfl⟩
    · simp [against, covers_singleton, kind] at hcov
    · have hle : s k ≤ s i := by
        simpa [against, step, covers_singleton, kind, Form.c] using hcov
      simp only [rank_step, if_true]
      rw [if_neg (not_lt.2 hle)]
      norm_num
    · have hle : s i ≤ s j := by
        simpa [against, step, covers_singleton, kind, Form.c] using hcov
      have hlt : s i < s j := lt_of_le_of_ne hle fun h => hj (hs.injective h).symm
      simp only [rank_step, if_true]
      rw [if_pos hlt]
      norm_num
    · simp [step, covers_singleton, kind] at hcov

/-- A strictly increasing scale of strengths inside `(0,1)`. -/
def humbleScale (j : ℕ) : ℚ := 1 - 1 / ((j : ℚ) + 2)

/-- **The staircase's hypothesis is inhabited within humble strengths.** -/
theorem humbleScale_spec : StrictMono humbleScale ∧ ∀ j, 0 < humbleScale j ∧ humbleScale j < 1 := by
  refine ⟨fun a b hab => ?_, fun j => ?_⟩
  · unfold humbleScale
    have ha : (0 : ℚ) < (a : ℚ) + 2 := by positivity
    have hab' : (a : ℚ) + 2 < (b : ℚ) + 2 := by exact_mod_cast Nat.add_lt_add_right hab 2
    have := one_div_lt_one_div_of_lt ha hab'
    linarith
  · unfold humbleScale
    have hj : (0 : ℚ) < (j : ℚ) + 2 := by positivity
    have h1 : 1 / ((j : ℚ) + 2) < 1 := by
      rw [div_lt_one hj]
      have : (0 : ℚ) ≤ (j : ℚ) := Nat.cast_nonneg j
      linarith
    have h2 : 0 < 1 / ((j : ℚ) + 2) := by positivity
    exact ⟨by linarith, by linarith⟩

/-! ## 3. Merging two case bases -/

/-- **The union of two case bases is rationalizable iff the union of their holdings has no
cycle**: merging reads the two holdings and not the cases. -/
theorem rationalizable_append_iff (Γ₁ Γ₂ : List (Case d)) :
    Rationalizable (Γ₁ ++ Γ₂) ↔
      ∀ U, ¬ Relation.TransGen (fun V U => Holding Γ₁ V U ∨ Holding Γ₂ V U) U U := by
  rw [rationalizable_iff_holding]
  have lift : ∀ V U, Holding Γ₁ V U ∨ Holding Γ₂ V U → Holding (Γ₁ ++ Γ₂) V U := by
    rintro V U (h | h)
    · exact holding_mono (fun c hc => List.mem_append_left _ hc) h
    · exact holding_mono (fun c hc => List.mem_append_right _ hc) h
  have fwd : ∀ V U, Relation.TransGen (fun V U => Holding Γ₁ V U ∨ Holding Γ₂ V U) V U →
      Holding (Γ₁ ++ Γ₂) V U := by
    intro V U h
    induction h with
    | single h => exact lift _ _ h
    | tail _ h ih => exact ih.trans (lift _ _ h)
  have bwd : ∀ V U, Holding (Γ₁ ++ Γ₂) V U →
      Relation.TransGen (fun V U => Holding Γ₁ V U ∨ Holding Γ₂ V U) V U := by
    intro V U h
    refine Relation.TransGen.mono (fun V U hd => ?_) h
    obtain ⟨c, hc, hb⟩ := hd
    rcases List.mem_append.1 hc with hc | hc
    · exact Or.inl (Relation.TransGen.single ⟨c, hc, hb⟩)
    · exact Or.inr (Relation.TransGen.single ⟨c, hc, hb⟩)
  exact ⟨fun h U hU => h U (fwd U U hU), fun h U hU => h U (bwd U U hU)⟩

/-- **Merged discord.**  The precedent — `P(X) ≥ 3/4` over `P(¬X) ≥ 1/2` — and the reverse
decision at `2/5` over `4/5` are each rationalizable alone, and their union is not. -/
theorem merged_discord :
    Rationalizable [precedent] ∧ Rationalizable [forbidden] ∧
      ¬ Rationalizable ([precedent] ++ [forbidden]) :=
  ⟨precedent_rationalizable, rationalizable_of_rank (fun _ => 0) (by decide +kernel),
    fun h => (by decide +kernel : ¬ Consistent ([precedent] ++ [forbidden])) h.consistent⟩

/-- The first two cases of `PrecedentConstraint.cycle`: `X` over `¬X`, `¬X` over `D`. -/
def cycleHead : List (Case 3) :=
  [⟨[Form.premise 0 (1/2)], [Form.premise 1 (1/2)]⟩,
   ⟨[Form.premise 1 (1/2)], [Form.premise 2 (1/2)]⟩]

/-- Its third case: `D` over `X`. -/
def cycleLast : List (Case 3) := [⟨[Form.premise 2 (1/2)], [Form.premise 0 (1/2)]⟩]

/-- **Hidden merged discord.**  Two rationalizable case bases whose union passes the pairwise
check and is not rationalizable. -/
theorem merged_discord_hidden :
    Rationalizable cycleHead ∧ Rationalizable cycleLast ∧ Consistent (cycleHead ++ cycleLast) ∧
      ¬ Rationalizable (cycleHead ++ cycleLast) :=
  ⟨rationalizable_of_rank
      (fun c => if c = ⟨[Form.premise 0 (1/2)], [Form.premise 1 (1/2)]⟩ then 0 else 1)
      (by decide +kernel),
    rationalizable_of_rank (fun _ => 0) (by decide +kernel),
    cycle_not_rationalizable.1, cycle_not_rationalizable.2⟩

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.PrecedentHolding.dominates_cons
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.Dominates.covers_left
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.Dominates.covers_right
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.Holding
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.Holding.trans
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.Holding.covers_left
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.Holding.covers_right
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.rationalizable_iff_holding
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.holding_mono
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.Reach
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.Reach.refl
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.Reach.trans
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.holding_cons
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.reach_cons
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.reach_mono
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.permitted_iff
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.permitted_congr
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.holding_append_congr
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.permitted_append_congr
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.permission_eq_iff_reach_eq
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.reach_cons_of_covers
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.holding_nil
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.vacuous
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.holding_not_minimal
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.AgreeOn
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.agreeOn_cons
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.reachSet
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.mem_reachSet
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.reachSet_eventually_const
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.permission_eventually_const
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.covers_singleton
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.step
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.against
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.staircase
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.staircase_irredundant
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.humbleScale
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.humbleScale_spec
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.rationalizable_append_iff
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.merged_discord
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.cycleHead
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.cycleLast
#print axioms Workspace.Normativity.Contrib.PrecedentHolding.merged_discord_hidden

end Workspace.Normativity.Contrib.PrecedentHolding
