/-
# Recollection as a stochastic map between world spaces

Round `projects/normativity/rounds/2026-11-08-content-recollection/`, matter 3, to fixture
level.

**The level chosen is world distributions.**  A **recollection** (`Recollection n n'`) is a
stochastic map from `n'` new worlds to `n` old worlds: `k w' w` is the weight with which new
world `w'` is retold as old world `w`; a function between worlds is the `0/1` case (`ofMap`).
On the coordinates "probability of a world" it is a `Conservativity.Translation`
(`toTranslation`), so matter 1 applies unchanged: an old row pulls back to a new row (`pull`),
valid at the pushed-forward credence iff its pullback is valid at the new credence
(`pull_sound`).  At the level of sentence prices an old sentence pulls back to the function
`w' ↦ Σ_{w ∈ S} k w' w`, which is a row over new world coordinates and a new sentence only
when it is `0/1`-valued; `split_pull` and `abandon_no_sentence` are the two cases.

§1: push, pull, the excess of a row (`excess_pull`), composition (`comp`, `push_comp`,
`pull_comp`).  §2: a recollection is a transport step with constant `1` and slack `0`
(`recollection_step`: the equality `excess_pull` written as an inequality, with no defect
measure of its own), two compose through `NormativeInductor.affine_transport_compose` to
`(1 · 1, 0 + 1 · 0)` (`recollection_chain`), and two recollections agreeing off a set of new
worlds move a row's excess by at most the row's oscillation times the mass on that set
(`approx_step`).  §3: composing a process with a recollection is a garbling of the process in
`ThinLegitimacy`'s sense (`garbling_of_recollection`).  §4: the **broken commitments** are the
rows the old region forces whose pullback the new region does not (`Broken`); none is broken
iff the new region pushes forward into the old (`no_broken_iff`).

§5, fixtures.  **Split**: one old sentence becomes two new ones; its price row pulls back to a
row on their sum; a new region refines the old and adds `P(S) ≥ 3/5`
(`split_refines`, `split_adds`), another breaks `P(S) ≥ 1/2` (`split_broken`).
**Abandonment**: under a recollection that retells each new world as a mixture, the old
sentence has no exact image (`abandon_no_sentence`), the commitment `P(S) ≥ 9/10` is broken at
every new credence (`abandon_broken_everywhere`), `P(S) ≥ 1/2` becomes a constraint on the new
credence (`abandon_half`); under a constant recollection every old row is kept or broken at
every credence alike (`const_pull_sat`); for a row of oscillation one, a map failing on one new
world leaves a slack equal to that world's mass, attained (`partial_slack`).

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.Conservativity
import Workspace.Deference.Contrib.ThinLegitimacy

namespace Workspace.Normativity.Contrib.Recollection

open Workspace.Normativity.Contrib.NormativeInductorComposition
open Workspace.Normativity.Contrib.NormativeInductor
open Workspace.Normativity.Contrib.Conservativity
open Finset

variable {n n' n'' : ℕ}

/-! ## 1. Push, pull, composition -/

/-- **A recollection**: a stochastic map from the new worlds to the old. -/
structure Recollection (n n' : ℕ) where
  k : Fin n' → Fin n → ℚ
  nonneg : ∀ w' w, 0 ≤ k w' w
  sum_one : ∀ w', ∑ w, k w' w = 1

namespace Recollection

/-- The recollection of a function between worlds. -/
def ofMap (f : Fin n' → Fin n) : Recollection n n' where
  k w' w := if f w' = w then 1 else 0
  nonneg _ _ := by split_ifs <;> norm_num
  sum_one w' := by simp

/-- A recollection as a translation of the coordinates "probability of a world". -/
def toTranslation (K : Recollection n n') : Translation n n' := fun w w' => K.k w' w

/-- **The pushforward** of a new credence: the old credence it recollects. -/
def push (K : Recollection n n') (q : Fin n' → ℚ) : Fin n → ℚ := K.toTranslation.apply q

/-- **The pullback of an old row**: a row over the new world coordinates. -/
def pull (K : Recollection n n') (r : Row n) : Row n' := Conservativity.pull K.toTranslation r

/-- **Soundness of the pullback**: an old row is valid at the pushed-forward credence iff its
pullback is valid at the new credence. -/
theorem pull_sound (K : Recollection n n') (r : Row n) (q : Fin n' → ℚ) :
    (K.pull r).Sat q ↔ r.Sat (K.push q) :=
  pull_sat_iff _ _ _

theorem push_nonneg (K : Recollection n n') {q : Fin n' → ℚ} (hq : ∀ w', 0 ≤ q w') (w : Fin n) :
    0 ≤ K.push q w :=
  Finset.sum_nonneg fun w' _ => mul_nonneg (K.nonneg w' w) (hq w')

/-- The pushforward preserves total mass. -/
theorem push_sum (K : Recollection n n') (q : Fin n' → ℚ) : ∑ w, K.push q w = ∑ w', q w' := by
  unfold push Translation.apply toTranslation
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w' _ => ?_
  rw [← Finset.sum_mul, K.sum_one, one_mul]

/-- Composition: retell the newest worlds as the middle ones, then those as the old. -/
def comp (K : Recollection n n') (K' : Recollection n' n'') : Recollection n n'' where
  k w'' w := ∑ w', K'.k w'' w' * K.k w' w
  nonneg _ _ := Finset.sum_nonneg fun _ _ => mul_nonneg (K'.nonneg _ _) (K.nonneg _ _)
  sum_one w'' := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, K.sum_one, mul_one, K'.sum_one]

theorem push_comp (K : Recollection n n') (K' : Recollection n' n'') (q : Fin n'' → ℚ) :
    (K.comp K').push q = K.push (K'.push q) := by
  funext w
  unfold push Translation.apply toTranslation comp
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun w' _ => Finset.sum_congr rfl fun w'' _ => by ring

theorem pull_comp (K : Recollection n n') (K' : Recollection n' n'') (r : Row n) :
    (K.comp K').pull r = K'.pull (K.pull r) := by
  unfold pull Conservativity.pull toTranslation comp
  congr 1
  funext w''
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun w' _ => Finset.sum_congr rfl fun w _ => by ring

end Recollection

open Recollection

/-- The **excess** of a row at a point: how far its left side exceeds its constant. -/
def excess {m : ℕ} (r : Row m) (x : Fin m → ℚ) : ℚ := ∑ i, r.a i * x i - r.b

theorem sat_iff_excess {m : ℕ} (r : Row m) (x : Fin m → ℚ) : r.Sat x ↔ excess r x ≤ 0 := by
  unfold Row.Sat excess
  constructor <;> intro h <;> linarith

/-- The value of an old row at a pushed-forward credence, as a sum over new worlds. -/
lemma eval_push (K : Recollection n n') (r : Row n) (q : Fin n' → ℚ) :
    ∑ w, r.a w * K.push q w = ∑ w', q w' * ∑ w, r.a w * K.k w' w := by
  unfold Recollection.push Translation.apply Recollection.toTranslation
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun w' _ => Finset.sum_congr rfl fun w _ => by ring

/-- **The pullback carries the excess exactly.** -/
theorem excess_pull (K : Recollection n n') (r : Row n) (q : Fin n' → ℚ) :
    excess (K.pull r) q = excess r (K.push q) := by
  unfold excess
  rw [eval_push]
  unfold Recollection.pull Conservativity.pull Recollection.toTranslation
  simp only
  congr 1
  exact Finset.sum_congr rfl fun w' _ => by ring

/-! ## 2. A recollection as a transport step -/

/-- **A recollection is a transport step with constant `1` and slack `0`**: the old row's
excess at the recollected credence is at most `1 ·` the pullback's excess at the new credence
`+ 0` (with equality, `excess_pull`). -/
theorem recollection_step (K : Recollection n n') (r : Row n) (q : Fin n' → ℚ) :
    ((excess r (K.push q) : ℚ) : ℝ) ≤ 1 * ((excess (K.pull r) q : ℚ) : ℝ) + 0 := by
  rw [excess_pull]; simp

/-- **Two recollections compose in the affine-error monoid** to the step `(1 · 1, 0 + 1 · 0)`,
by `affine_transport_compose`. -/
theorem recollection_chain (K : Recollection n n') (K' : Recollection n' n'') (r : Row n)
    (q : Fin n'' → ℚ) :
    ((excess r ((K.comp K').push q) : ℚ) : ℝ) ≤
      (1 * 1) * ((excess (K'.pull (K.pull r)) q : ℚ) : ℝ) + (0 + 1 * 0) := by
  rw [push_comp]
  exact affine_transport_compose zero_le_one (recollection_step K' (K.pull r) q)
    (recollection_step K r (K'.push q))

/-- A row's value at a retold world lies between the row's coefficient bounds. -/
lemma retold_bounds (K : Recollection n n') (r : Row n) {lo hi : ℚ}
    (hr : ∀ i, lo ≤ r.a i ∧ r.a i ≤ hi) (w' : Fin n') :
    lo ≤ ∑ w, r.a w * K.k w' w ∧ ∑ w, r.a w * K.k w' w ≤ hi := by
  constructor
  · calc lo = ∑ w, lo * K.k w' w := by rw [← Finset.mul_sum, K.sum_one, mul_one]
      _ ≤ ∑ w, r.a w * K.k w' w :=
        Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (hr w).1 (K.nonneg w' w)
  · calc ∑ w, r.a w * K.k w' w ≤ ∑ w, hi * K.k w' w :=
        Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (hr w).2 (K.nonneg w' w)
      _ = hi := by rw [← Finset.mul_sum, K.sum_one, mul_one]

/-- **The approximate step.**  Two recollections that agree off a set `B` of new worlds move
an old row's excess by at most the row's oscillation times the new credence's mass on `B`: a
transport step with constant `1` and slack `(hi − lo) · q(B)`. -/
theorem approx_step (K K₀ : Recollection n n') (B : Finset (Fin n'))
    (hB : ∀ w', w' ∉ B → K.k w' = K₀.k w') (r : Row n) (lo hi : ℚ)
    (hr : ∀ i, lo ≤ r.a i ∧ r.a i ≤ hi) (q : Fin n' → ℚ) (hq : ∀ w', 0 ≤ q w') :
    excess r (K.push q) ≤ excess r (K₀.push q) + (hi - lo) * ∑ w' ∈ B, q w' := by
  unfold excess
  rw [eval_push, eval_push]
  have hterm : ∀ w', q w' * ∑ w, r.a w * K.k w' w ≤
      q w' * ∑ w, r.a w * K₀.k w' w + (if w' ∈ B then (hi - lo) * q w' else 0) := by
    intro w'
    by_cases hw : w' ∈ B
    · rw [if_pos hw]
      have h1 := (retold_bounds K r hr w').2
      have h2 := (retold_bounds K₀ r hr w').1
      nlinarith [hq w']
    · rw [if_neg hw, hB w' hw, add_zero]
  have hsum := Finset.sum_le_sum fun w' (_ : w' ∈ (univ : Finset (Fin n'))) => hterm w'
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum] at hsum
  linarith

/-! ## 3. The relation to `ThinLegitimacy`'s garbling -/

section Garbling

open Workspace.Deference.Contrib.ThinLegitimacy

/-- A process to the new worlds followed by a recollection: a process to the old worlds. -/
noncomputable def compKernel {Ω : Type*} (A : Kernel Ω (Fin n')) (K : Recollection n n') :
    Kernel Ω (Fin n) where
  k ω w := ∑ w', A.k ω w' * ((K.k w' w : ℚ) : ℝ)
  nonneg ω w := Finset.sum_nonneg fun w' _ =>
    mul_nonneg (A.nonneg ω w') (by exact_mod_cast K.nonneg w' w)
  sum_one ω := by
    rw [Finset.sum_comm]
    have h : ∀ w', ∑ w, A.k ω w' * ((K.k w' w : ℚ) : ℝ) = A.k ω w' := by
      intro w'
      rw [← Finset.mul_sum]
      have : ∑ w, ((K.k w' w : ℚ) : ℝ) = 1 := by exact_mod_cast K.sum_one w'
      rw [this, mul_one]
    simp only [h, A.sum_one]

/-- **A recollection exhibits the old-world process as a garbling of the new-world process**,
in `ThinLegitimacy.Garbling`'s own terms: the recollection, cast to the reals, is the
stochastic matrix. -/
theorem garbling_of_recollection {Ω : Type*} (A : Kernel Ω (Fin n')) (K : Recollection n n') :
    Garbling A (compKernel A K) :=
  ⟨fun w' w => ((K.k w' w : ℚ) : ℝ),
    fun w' w => by show (0 : ℝ) ≤ ((K.k w' w : ℚ) : ℝ); exact_mod_cast K.nonneg w' w,
    fun w' => by show ∑ w, ((K.k w' w : ℚ) : ℝ) = 1; exact_mod_cast K.sum_one w',
    fun _ _ => rfl⟩

end Garbling

/-! ## 4. Broken commitments -/

/-- **A broken commitment**: a row the old region forces whose pullback the new region does
not. -/
def Broken (K : Recollection n n') (R : (Fin n → ℚ) → Prop) (R' : (Fin n' → ℚ) → Prop)
    (r : Row n) : Prop :=
  Forces R r ∧ ¬ Forces R' (K.pull r)

/-- **No commitment is broken iff the new region pushes forward into the old.** -/
theorem no_broken_iff {Q : Type*} (K : Recollection n n') (B : Bundle Q n)
    (R' : (Fin n' → ℚ) → Prop) :
    (∀ r, ¬ Broken K B.Region R' r) ↔ ∀ q, R' q → B.Region (K.push q) := by
  have h := refines_iff K.toTranslation B R'
  constructor
  · intro hb q hq
    refine h.1 (fun r hr => ?_) _ ⟨q, hq, rfl⟩
    by_contra hno
    exact hb r ⟨hr, hno⟩
  · rintro hq r ⟨hr, hno⟩
    exact hno fun q hq' => (K.pull_sound r q).2 (hr _ (hq q hq'))

/-! ## 5. Fixtures -/

/-! ### Split: one old sentence becomes two -/

/-- Old worlds `(S, ¬S)`; new worlds `(S₁, S₂, neither)`; both new sentences retell as `S`. -/
def split : Recollection 2 3 := ofMap ![0, 0, 1]

theorem split_push (q : Fin 3 → ℚ) : split.push q = ![q 0 + q 1, q 2] := by
  funext w
  fin_cases w <;>
    simp [split, Recollection.push, Translation.apply, Recollection.toTranslation,
      Recollection.ofMap, Fin.sum_univ_three]

/-- The old row `P(S) ≥ c`. -/
def atLeast (c : ℚ) : Row 2 := ⟨![-1, 0], -c⟩

/-- **The old sentence's price row pulls back to a row on the sum of the two new sentences**:
`P(S) ≥ c` becomes `P(S₁) + P(S₂) ≥ c`. -/
theorem split_pull (c : ℚ) (q : Fin 3 → ℚ) : (split.pull (atLeast c)).Sat q ↔ c ≤ q 0 + q 1 := by
  rw [pull_sound, split_push]
  simp only [atLeast, Row.Sat, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> intro h <;> linarith

/-- The old commitments: a credence over `(S, ¬S)` with `P(S) ≥ 1/2`. -/
def oldB : Bundle Unit 2 :=
  [⟨(), ⟨![1, 1], 1⟩⟩, ⟨(), ⟨![-1, -1], -1⟩⟩, ⟨(), atLeast (1/2)⟩]

/-- New commitments: a credence over the three worlds with `P(S₁) ≥ a`, `P(S₂) ≥ b`. -/
def newB (a b : ℚ) : Bundle Unit 3 :=
  [⟨(), ⟨![1, 1, 1], 1⟩⟩, ⟨(), ⟨![-1, -1, -1], -1⟩⟩, ⟨(), ⟨![-1, 0, 0], -a⟩⟩,
    ⟨(), ⟨![0, -1, 0], -b⟩⟩]

lemma oldB_region (x : Fin 2 → ℚ) :
    oldB.Region x ↔ InCube x ∧ x 0 + x 1 = 1 ∧ 1/2 ≤ x 0 := by
  unfold Bundle.Region oldB atLeast
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Row.Sat,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨hc, h1, h2, h3⟩; exact ⟨hc, by linarith, by linarith⟩
  · rintro ⟨hc, h1, h2⟩; exact ⟨hc, by linarith, by linarith, by linarith⟩

lemma newB_region (a b : ℚ) (q : Fin 3 → ℚ) :
    (newB a b).Region q ↔ InCube q ∧ q 0 + q 1 + q 2 = 1 ∧ a ≤ q 0 ∧ b ≤ q 1 := by
  unfold Bundle.Region newB
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Row.Sat,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  constructor
  · rintro ⟨hc, h1, h2, h3, h4⟩; exact ⟨hc, by linarith, by linarith, by linarith⟩
  · rintro ⟨hc, h1, h2, h3⟩; exact ⟨hc, by linarith, by linarith, by linarith, by linarith⟩

/-- A new region with `a + b ≥ 1/2` pushes forward into the old region. -/
lemma split_into_old {a b : ℚ} (hab : 1/2 ≤ a + b) {q : Fin 3 → ℚ} (hq : (newB a b).Region q) :
    oldB.Region (split.push q) := by
  rw [newB_region] at hq
  obtain ⟨hc, h1, ha, hb⟩ := hq
  rw [oldB_region, split_push]
  refine ⟨fun i => ?_, by simp; linarith, by simp; linarith⟩
  fin_cases i
  · simp; exact ⟨by linarith [(hc 0).1, (hc 1).1], by linarith [(hc 2).1]⟩
  · simpa using hc 2

/-- **The split refines**: with `P(S₁) ≥ 2/5` and `P(S₂) ≥ 1/5` no old commitment is broken. -/
theorem split_refines :
    Refines split.toTranslation oldB.Region (newB (2/5) (1/5)).Region :=
  (refines_iff _ oldB _).2 fun _ ⟨_, hq, hx⟩ => hx ▸ split_into_old (by norm_num) hq

/-- **And it adds a commitment in the old vocabulary**: the pullback of `P(S) ≥ 3/5` is forced
by the new region, and the old region does not force `P(S) ≥ 3/5`. -/
theorem split_adds :
    ¬ AddsNothing split.toTranslation oldB.Region (newB (2/5) (1/5)).Region := by
  intro h
  have hold := h (atLeast (3/5)) (fun q hq => by
    rw [newB_region] at hq
    exact (split_pull _ q).2 (by linarith [hq.2.2.1, hq.2.2.2]))
  have hx : oldB.Region ![1/2, 1/2] := by decide +kernel
  have := hold _ hx
  simp [atLeast, Row.Sat, Fin.sum_univ_two] at this
  norm_num at this

/-- **A broken commitment**: with `P(S₁) ≥ 1/5` and `P(S₂) ≥ 1/5` the old commitment
`P(S) ≥ 1/2` is forced by the old region and its pullback is not forced by the new. -/
theorem split_broken :
    Broken split oldB.Region (newB (1/5) (1/5)).Region (atLeast (1/2)) := by
  refine ⟨fun x hx => ?_, fun h => ?_⟩
  · rw [oldB_region] at hx
    simp only [atLeast, Row.Sat, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith [hx.2.2]
  · have hq : (newB (1/5) (1/5)).Region ![1/5, 1/5, 3/5] := by decide +kernel
    have := (split_pull _ _).1 (h _ hq)
    norm_num at this

/-! ### Abandonment: an old sentence with no exact image -/

/-- Each new world retells as a mixture: the first as `S` with weight `1/4`, the second with
weight `3/4`. -/
def abandon : Recollection 2 2 where
  k := ![![1/4, 3/4], ![3/4, 1/4]]
  nonneg w' w := by fin_cases w' <;> fin_cases w <;> norm_num
  sum_one w' := by fin_cases w' <;> simp [Fin.sum_univ_two] <;> norm_num

/-- **The old sentence has no exact image**: no set of new worlds has the old sentence's
pullback as its indicator. -/
theorem abandon_no_sentence :
    ¬ ∃ S' : Finset (Fin 2), ∀ w', abandon.k w' 0 = if w' ∈ S' then 1 else 0 := by
  rintro ⟨S', h⟩
  have := h 0
  simp only [abandon, Matrix.cons_val_zero] at this
  split_ifs at this <;> norm_num at this

theorem abandon_push (q : Fin 2 → ℚ) :
    abandon.push q = ![1/4 * q 0 + 3/4 * q 1, 3/4 * q 0 + 1/4 * q 1] := by
  funext w
  fin_cases w <;>
    simp [abandon, Recollection.push, Translation.apply, Recollection.toTranslation,
      Fin.sum_univ_two]

/-- **The commitment `P(S) ≥ 9/10` is broken at every new credence.** -/
theorem abandon_broken_everywhere (q : Fin 2 → ℚ) (hq : ∀ w', 0 ≤ q w') (h1 : q 0 + q 1 = 1) :
    ¬ (abandon.pull (atLeast (9/10))).Sat q := by
  rw [pull_sound, abandon_push]
  simp only [atLeast, Row.Sat, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have := hq 0
  have := hq 1
  intro h
  linarith

/-- **The commitment `P(S) ≥ 1/2` becomes a constraint on the new credence**: its pullback
holds iff the second new world has probability at least `1/2`. -/
theorem abandon_half (q : Fin 2 → ℚ) (h1 : q 0 + q 1 = 1) :
    (abandon.pull (atLeast (1/2))).Sat q ↔ 1/2 ≤ q 1 := by
  rw [pull_sound, abandon_push]
  simp only [atLeast, Row.Sat, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> intro h <;> linarith

/-- The constant recollection: every new world retells as the same old credence `π`. -/
def const (π : Fin n → ℚ) (hπ : ∀ w, 0 ≤ π w) (h1 : ∑ w, π w = 1) : Recollection n n' :=
  ⟨fun _ w => π w, fun _ w => hπ w, fun _ => h1⟩

/-- **Under a constant recollection an old row is kept or broken at every new credence alike**:
its pullback holds at a new credence of total mass one iff the row holds at `π`. -/
theorem const_pull_sat (π : Fin n → ℚ) (hπ : ∀ w, 0 ≤ π w) (h1 : ∑ w, π w = 1) (r : Row n)
    (q : Fin n' → ℚ) (hq : ∑ w', q w' = 1) :
    ((const π hπ h1 : Recollection n n').pull r).Sat q ↔ r.Sat π := by
  rw [pull_sound]
  have : (const π hπ h1 : Recollection n n').push q = π := by
    funext w
    unfold Recollection.push Translation.apply Recollection.toTranslation const
    simp only
    rw [← Finset.mul_sum, hq, mul_one]
  rw [this]

/-- Two maps on three new worlds that differ on the third alone: it retells as `S` under the
first and as `¬S` under the second. -/
def partial₁ : Recollection 2 3 := ofMap ![0, 1, 0]
def partial₀ : Recollection 2 3 := ofMap ![0, 1, 1]

/-- **The slack is the mass on which the map fails, and it is attained**: the excess of
`P(S) ≥ c` under the two completions differs by exactly the third world's mass. -/
theorem partial_slack (c : ℚ) (q : Fin 3 → ℚ) (hq : ∀ w', 0 ≤ q w') :
    excess (atLeast c) (partial₀.push q) ≤
        excess (atLeast c) (partial₁.push q) + (0 - (-1)) * ∑ w' ∈ ({2} : Finset (Fin 3)), q w' ∧
      excess (atLeast c) (partial₀.push q) = excess (atLeast c) (partial₁.push q) + q 2 := by
  refine ⟨approx_step partial₀ partial₁ {2} (fun w' hw => ?_) (atLeast c) (-1) 0 (fun i => ?_) q hq,
    ?_⟩
  · fin_cases w'
    · rfl
    · rfl
    · exact absurd (Finset.mem_singleton_self _) hw
  · fin_cases i <;> simp [atLeast]
  · simp [excess, atLeast, partial₀, partial₁, Recollection.push, Translation.apply,
      Recollection.toTranslation, Recollection.ofMap, Fin.sum_univ_two, Fin.sum_univ_three]
    ring

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.Recollection.Recollection
#print axioms Workspace.Normativity.Contrib.Recollection.Recollection.ofMap
#print axioms Workspace.Normativity.Contrib.Recollection.Recollection.toTranslation
#print axioms Workspace.Normativity.Contrib.Recollection.Recollection.push
#print axioms Workspace.Normativity.Contrib.Recollection.Recollection.pull
#print axioms Workspace.Normativity.Contrib.Recollection.Recollection.pull_sound
#print axioms Workspace.Normativity.Contrib.Recollection.Recollection.push_nonneg
#print axioms Workspace.Normativity.Contrib.Recollection.Recollection.push_sum
#print axioms Workspace.Normativity.Contrib.Recollection.Recollection.comp
#print axioms Workspace.Normativity.Contrib.Recollection.Recollection.push_comp
#print axioms Workspace.Normativity.Contrib.Recollection.Recollection.pull_comp
#print axioms Workspace.Normativity.Contrib.Recollection.excess
#print axioms Workspace.Normativity.Contrib.Recollection.sat_iff_excess
#print axioms Workspace.Normativity.Contrib.Recollection.eval_push
#print axioms Workspace.Normativity.Contrib.Recollection.excess_pull
#print axioms Workspace.Normativity.Contrib.Recollection.recollection_step
#print axioms Workspace.Normativity.Contrib.Recollection.recollection_chain
#print axioms Workspace.Normativity.Contrib.Recollection.retold_bounds
#print axioms Workspace.Normativity.Contrib.Recollection.approx_step
#print axioms Workspace.Normativity.Contrib.Recollection.compKernel
#print axioms Workspace.Normativity.Contrib.Recollection.garbling_of_recollection
#print axioms Workspace.Normativity.Contrib.Recollection.Broken
#print axioms Workspace.Normativity.Contrib.Recollection.no_broken_iff
#print axioms Workspace.Normativity.Contrib.Recollection.split
#print axioms Workspace.Normativity.Contrib.Recollection.split_push
#print axioms Workspace.Normativity.Contrib.Recollection.atLeast
#print axioms Workspace.Normativity.Contrib.Recollection.split_pull
#print axioms Workspace.Normativity.Contrib.Recollection.oldB
#print axioms Workspace.Normativity.Contrib.Recollection.newB
#print axioms Workspace.Normativity.Contrib.Recollection.oldB_region
#print axioms Workspace.Normativity.Contrib.Recollection.newB_region
#print axioms Workspace.Normativity.Contrib.Recollection.split_into_old
#print axioms Workspace.Normativity.Contrib.Recollection.split_refines
#print axioms Workspace.Normativity.Contrib.Recollection.split_adds
#print axioms Workspace.Normativity.Contrib.Recollection.split_broken
#print axioms Workspace.Normativity.Contrib.Recollection.abandon
#print axioms Workspace.Normativity.Contrib.Recollection.abandon_no_sentence
#print axioms Workspace.Normativity.Contrib.Recollection.abandon_push
#print axioms Workspace.Normativity.Contrib.Recollection.abandon_broken_everywhere
#print axioms Workspace.Normativity.Contrib.Recollection.abandon_half
#print axioms Workspace.Normativity.Contrib.Recollection.const
#print axioms Workspace.Normativity.Contrib.Recollection.const_pull_sat
#print axioms Workspace.Normativity.Contrib.Recollection.partial₁
#print axioms Workspace.Normativity.Contrib.Recollection.partial₀
#print axioms Workspace.Normativity.Contrib.Recollection.partial_slack

end Workspace.Normativity.Contrib.Recollection
