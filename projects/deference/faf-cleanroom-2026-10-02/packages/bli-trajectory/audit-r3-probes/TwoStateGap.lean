import Cleanroom.Bli.BliTrajectory.TriState

/-!
# Audit r3 (adversarial) probe — `bli-trajectory`: with two *distinct* coherent tables, faith in
the marginal **as defined** (`FaithMarginal`, scope `Sminus m m`) does not imply `E2x`

Not imported by the library. The package says (ledger row `faithMarginal_not_imp_e2x`, findings
F-13/F-20, report §M7 (iii) step 2) that "with two *distinct* additive tables the converse
holds (`Pinning.two_state_pinning_scope`), and the distinct-table refutation needs three states
(`TriState`)". `two_state_pinning_scope` needs faith on a family **closed under `⋏` and `∼`**.
`FaithMarginal` quantifies over `Sminus m m`, which is size-bounded: at `(n, m) = (0, 1)` it
contains `atom 0` and `atom 1` but not `atom 0 ⋏ atom 1` (`sizeBound 1 = 4`; a conjunction of
two atoms has `tokenSize ≥ 8`). This probe exploits exactly that gap.

**The witness.** Two atoms `a = atom 0`, `b = atom 1` cut each day's worlds into four cells; the
day-`n` worlds `gapWorld n k` hold the day-`(n+1)` candidate `c₁` (`k = 0, 1`) or `c₂` (`k = 2, 3`)
and the cell `{a, b}`, `{a}`, `{b}`, `∅` respectively. The day-`(n+1)` tables are the two
unskewed cell mixtures (`c₁ ↦ ½ w₀ + ½ w₁`, `c₂ ↦ ½ w₂ + ½ w₃`): they are coherent, each knows its
own state atom, and they **differ** (`a ↦ 1` vs `a ↦ 0`). The market on day `0` is the mixture
with weights `¼ + δ, ¼ − δ, ¼ − δ, ¼ + δ` — the conditional given `c₁` is skewed on `b` — and on
every later day the unskewed mixture (so constraint 2 holds there on every sentence). Then:

* every `φ ∈ Sminus 1 1` is atom-free or a single atom (`shape_of_tokenSize_le_four`), on which
  the skew is invisible to faith in the marginal (`gapHistory_faith_zero`);
* `FaithMarginal`, `E1x`, `E3`, `E4`, `E5` hold on the full scope, market, base and every table
  are `CoherentOn ∅ A` for every `A`, the two tables of every day are distinct, and `E2x` fails at
  `(0, 1, c₁ 1, atom 1)`: `𝐏_0(b ⋏ σ₁) = ¼ + δ ≠ ½ · ½` (`two_state_distinct_coherent_gap`);
* faith **fails** at `a ⋏ b`, which is outside `Sminus 1 1` (`gap_faith_fails_outside_scope`,
  `and_not_mem_Sminus`): the witness lives on the scope gap, as the Pinning theorem predicts.

So the claim "needs three states" is true for faith on a Boolean-closed scope (the Notion's
reading) and false for the package's predicate of record; the package's text does not keep the
two apart. The same scaffold as the package's witnesses (no state atom of a day `≥ n+2` holds).
-/

namespace Cleanroom.Bli.BliTrajectory.AuditR3

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory

open Classical

noncomputable section

/-- The second atom, `atom 1` (= `TriState.triAtom'`). -/
def gapAtom : Sentence := Formula.atom 1

/-- The four worlds at day `n`: candidate `c₁` with cell `{a, b}` / `{a}`, candidate `c₂` with
cell `{b}` / `∅`. No state atom of a day `≠ n+1` holds (the package's scaffold). -/
def gapWorld (n : ℕ) : Fin 4 → PCWorld
  | 0 => fun x => x = stateCode (n + 1) (c₁ (n + 1)) ∨ x = 0 ∨ x = 1
  | 1 => fun x => x = stateCode (n + 1) (c₁ (n + 1)) ∨ x = 0
  | 2 => fun x => x = stateCode (n + 1) (c₂ (n + 1)) ∨ x = 1
  | 3 => fun x => x = stateCode (n + 1) (c₂ (n + 1))

/-- Weights `¼ + δ, ¼ − δ, ¼ − δ, ¼ + δ`. -/
def gapWeight (δ : ℝ) : Fin 4 → ℝ
  | 0 => 1 / 4 + δ
  | 1 => 1 / 4 - δ
  | 2 => 1 / 4 - δ
  | 3 => 1 / 4 + δ

/-- The skew is applied on day `0` only. -/
def gapSkew (δ : ℝ) (n : ℕ) : ℝ := if n = 0 then δ else 0

/-- The market: on day `n` the mixture of the four worlds with the (possibly skewed) weights. -/
def gapHistory (δ : ℝ) : History :=
  fun n φ => ∑ k : Fin 4, gapWeight (gapSkew δ n) k * (gapWorld n k).payout φ

/-- The day-`m` table of candidate `q`: the unskewed mixture over its two cells. -/
def gapTable (m q : ℕ) (φ : Sentence) : ℝ :=
  if q = c₁ m then
    (1 / 2 : ℝ) * (gapWorld (m - 1) 0).payout φ + (1 / 2 : ℝ) * (gapWorld (m - 1) 1).payout φ
  else
    (1 / 2 : ℝ) * (gapWorld (m - 1) 2).payout φ + (1 / 2 : ℝ) * (gapWorld (m - 1) 3).payout φ

/-- The two-state system: codes `twoCodes`, tables `gapTable`, realized state `c₁`. -/
def gapSystem : StateSystem where
  states := twoCodes
  val := gapTable
  actual m := 4 ^ sizeBound m
  actual_mem _ := by simp [twoCodes]

variable {δ : ℝ} {n : ℕ}

lemma gapSystem_states (m : ℕ) : gapSystem.states m = {c₁ m, c₂ m} := rfl

/-! ## Payouts -/

lemma gapWorld_payout_state (n : ℕ) :
    ((gapWorld n 0).payout (stateAtom (n + 1) (c₁ (n + 1))) = 1 ∧
      (gapWorld n 1).payout (stateAtom (n + 1) (c₁ (n + 1))) = 1 ∧
      (gapWorld n 2).payout (stateAtom (n + 1) (c₁ (n + 1))) = 0 ∧
      (gapWorld n 3).payout (stateAtom (n + 1) (c₁ (n + 1))) = 0) ∧
    ((gapWorld n 0).payout (stateAtom (n + 1) (c₂ (n + 1))) = 0 ∧
      (gapWorld n 1).payout (stateAtom (n + 1) (c₂ (n + 1))) = 0 ∧
      (gapWorld n 2).payout (stateAtom (n + 1) (c₂ (n + 1))) = 1 ∧
      (gapWorld n 3).payout (stateAtom (n + 1) (c₂ (n + 1))) = 1) := by
  have h0 : ∀ q, stateCode (n + 1) q ≠ 0 := fun q => (zero_ne_stateCode _ q).symm
  have h1 : ∀ q, stateCode (n + 1) q ≠ 1 := fun q => (one_ne_stateCode _ q).symm
  have h12 : stateCode (n + 1) (c₁ (n + 1)) ≠ stateCode (n + 1) (c₂ (n + 1)) :=
    fun h => c₁_ne_c₂ (n + 1) (stateCode_inj.mp h).2
  have h21 : stateCode (n + 1) (c₂ (n + 1)) ≠ stateCode (n + 1) (c₁ (n + 1)) := h12.symm
  simp only [stateAtom_eq_atom]
  simp [PCWorld.payout, gapWorld, h0, h1, h12, h21]

lemma gapWorld_payout_cohAtom (n : ℕ) :
    (gapWorld n 0).payout cohAtom = 1 ∧ (gapWorld n 1).payout cohAtom = 1 ∧
      (gapWorld n 2).payout cohAtom = 0 ∧ (gapWorld n 3).payout cohAtom = 0 := by
  have h0 : ∀ q, (0 : ℕ) ≠ stateCode (n + 1) q := fun q => zero_ne_stateCode _ q
  simp [PCWorld.payout, gapWorld, cohAtom, h0]

lemma gapWorld_payout_gapAtom (n : ℕ) :
    (gapWorld n 0).payout gapAtom = 1 ∧ (gapWorld n 1).payout gapAtom = 0 ∧
      (gapWorld n 2).payout gapAtom = 1 ∧ (gapWorld n 3).payout gapAtom = 0 := by
  have h1 : ∀ q, (1 : ℕ) ≠ stateCode (n + 1) q := fun q => one_ne_stateCode _ q
  simp [PCWorld.payout, gapWorld, gapAtom, h1]

lemma gapWorld_payout_stateAtom_ne {m : ℕ} (hm : m ≠ n + 1) (q : ℕ) (k : Fin 4) :
    (gapWorld n k).payout (stateAtom m q) = 0 := by
  have h0 : stateCode m q ≠ 0 := (zero_ne_stateCode m q).symm
  have h1 : stateCode m q ≠ 1 := (one_ne_stateCode m q).symm
  have h2 : ∀ q', stateCode m q ≠ stateCode (n + 1) q' := fun q' h => hm (stateCode_inj.mp h).1
  rw [stateAtom_eq_atom]
  fin_cases k <;> simp [PCWorld.payout, gapWorld, h0, h1, h2]

lemma gapWorld_payout_atom_other {a : ℕ} (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hday : atomDay a < n + 1) (k : Fin 4) : (gapWorld n k).payout (Formula.atom a) = 0 := by
  have h2 : ∀ q, a ≠ stateCode (n + 1) q := by
    intro q h
    have := atomDay_stateAtom (n + 1) q a
      (by rw [sentenceAtomCodes_stateAtom, h]; exact Finset.mem_singleton_self _)
    omega
  fin_cases k <;> simp [PCWorld.payout, gapWorld, ha0, ha1, h2]

/-- An atom-free sentence has the same payout in every world. -/
lemma payout_congr_of_atomFree {φ : Sentence} (h : sentenceAtomCodes φ = ∅) (v w : PCWorld) :
    v.payout φ = w.payout φ := by
  have key : v.Holds φ ↔ w.Holds φ :=
    PCWorld.holds_congr_atomCodes φ (fun a ha => by rw [h] at ha; simp at ha)
  unfold PCWorld.payout
  simp only [key]

/-! ## The size gap: `tokenSize ≤ 2` is atom-free, `tokenSize ≤ 4` is atom-free or one atom -/

lemma atomFree_of_tokenSize_le_two : ∀ φ : Sentence, tokenSize φ ≤ 2 → sentenceAtomCodes φ = ∅ := by
  intro φ
  induction φ using Formula.rec' with
  | hfalsum => intro _; rfl
  | hatom a =>
      intro h
      rw [tokenSize_atom, length_natDigits4_eq_log (by omega)] at h
      have : 0 < Nat.log 4 (a + 5) := Nat.log_pos (by norm_num) (by omega)
      omega
  | himp φ ψ ihφ ihψ =>
      intro h
      rw [tokenSize_imp] at h
      simp [ihφ (by omega), ihψ (by omega)]
  | hand φ ψ ihφ ihψ =>
      intro h
      rw [tokenSize_and] at h
      simp [ihφ (by omega), ihψ (by omega)]
  | hor φ ψ ihφ ihψ =>
      intro h
      rw [tokenSize_or] at h
      simp [ihφ (by omega), ihψ (by omega)]

lemma shape_of_tokenSize_le_four (φ : Sentence) (h : tokenSize φ ≤ 4) :
    sentenceAtomCodes φ = ∅ ∨ ∃ a, φ = Formula.atom a := by
  induction φ using Formula.rec' with
  | hfalsum => exact Or.inl rfl
  | hatom a => exact Or.inr ⟨a, rfl⟩
  | himp φ ψ _ _ =>
      left
      rw [tokenSize_imp] at h
      simp [atomFree_of_tokenSize_le_two φ (by omega), atomFree_of_tokenSize_le_two ψ (by omega)]
  | hand φ ψ _ _ =>
      left
      rw [tokenSize_and] at h
      simp [atomFree_of_tokenSize_le_two φ (by omega), atomFree_of_tokenSize_le_two ψ (by omega)]
  | hor φ ψ _ _ =>
      left
      rw [tokenSize_or] at h
      simp [atomFree_of_tokenSize_le_two φ (by omega), atomFree_of_tokenSize_le_two ψ (by omega)]

lemma pair_zero_one : Nat.pair 0 1 = 1 := by decide

lemma atomDay_one : atomDay 1 = 0 := by
  rw [← pair_zero_one]
  simp [atomDay, atomDayBase, cleanroomBaseTag, Nat.unpair_pair]

lemma gapAtom_mem_Sminus : gapAtom ∈ Sminus 1 1 := by
  rw [mem_Sminus]
  refine ⟨?_, fun a ha => ?_⟩
  · unfold SmallOn gapAtom
    rw [tokenSize_atom]
    have h := length_natDigits4_le_of_lt_pow (n := 1 + 5) (L := 2) (by norm_num)
    have := four_le_sizeBound (le_refl 1)
    omega
  · simp only [gapAtom, sentenceAtomCodes_atom, Finset.mem_singleton] at ha
    subst ha
    rw [atomDay_one]
    omega

/-- `atom 0 ⋏ atom 1 ∉ Sminus 1 1`: the scope at `(0, 1)` is not closed under `⋏`. -/
lemma and_not_mem_Sminus : (cohAtom ⋏ gapAtom) ∉ Sminus 1 1 := by
  rw [mem_Sminus]
  rintro ⟨h, -⟩
  unfold SmallOn cohAtom gapAtom at h
  rw [tokenSize_and, tokenSize_atom, tokenSize_atom] at h
  have h1 := one_le_length_natDigits4 (n := 0 + 5) (by norm_num)
  have h2 := one_le_length_natDigits4 (n := 1 + 5) (by norm_num)
  have : sizeBound 1 = 4 := by norm_num [sizeBound]
  omega

/-! ## The market on the sentences the constraints read -/

lemma gapHistory_and_state (n : ℕ) (φ : Sentence) :
    gapHistory δ n (φ ⋏ stateAtom (n + 1) (c₁ (n + 1))) =
        gapWeight (gapSkew δ n) 0 * (gapWorld n 0).payout φ +
          gapWeight (gapSkew δ n) 1 * (gapWorld n 1).payout φ ∧
      gapHistory δ n (φ ⋏ stateAtom (n + 1) (c₂ (n + 1))) =
        gapWeight (gapSkew δ n) 2 * (gapWorld n 2).payout φ +
          gapWeight (gapSkew δ n) 3 * (gapWorld n 3).payout φ := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩ := gapWorld_payout_state n
  constructor
  · simp only [gapHistory, Fin.sum_univ_four, payout_and, a0, a1, a2, a3]; ring
  · simp only [gapHistory, Fin.sum_univ_four, payout_and, b0, b1, b2, b3]; ring

lemma gapHistory_state (n : ℕ) :
    gapHistory δ n (stateAtom (n + 1) (c₁ (n + 1))) = 1 / 2 ∧
      gapHistory δ n (stateAtom (n + 1) (c₂ (n + 1))) = 1 / 2 := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩ := gapWorld_payout_state n
  constructor
  · simp only [gapHistory, Fin.sum_univ_four, a0, a1, a2, a3, gapWeight]; ring
  · simp only [gapHistory, Fin.sum_univ_four, b0, b1, b2, b3, gapWeight]; ring

lemma gapHistory_stateAtom_ne {m : ℕ} (hm : m ≠ n + 1) (q : ℕ) :
    gapHistory δ n (stateAtom m q) = 0 := by
  simp only [gapHistory, Fin.sum_univ_four, gapWorld_payout_stateAtom_ne hm]; ring

lemma gapHistory_and_stateAtom_ne {m : ℕ} (hm : m ≠ n + 1) (q : ℕ) (φ : Sentence) :
    gapHistory δ n (φ ⋏ stateAtom m q) = 0 := by
  simp only [gapHistory, Fin.sum_univ_four, payout_and, gapWorld_payout_stateAtom_ne hm]; ring

lemma gapHistory_and_two_ne {o : ℕ} (ho : o ≠ n + 1) (m q₁ q₂ : ℕ) (φ : Sentence) :
    gapHistory δ n (φ ⋏ (stateAtom m q₁ ⋏ stateAtom o q₂)) = 0 := by
  simp only [gapHistory, Fin.sum_univ_four, payout_and, gapWorld_payout_stateAtom_ne ho]; ring

lemma gapHistory_two_ne {o : ℕ} (ho : o ≠ n + 1) (m q₁ q₂ : ℕ) :
    gapHistory δ n (stateAtom m q₁ ⋏ stateAtom o q₂) = 0 := by
  simp only [gapHistory, Fin.sum_univ_four, payout_and, gapWorld_payout_stateAtom_ne ho]; ring

lemma gapHistory_excl (n : ℕ) :
    gapHistory δ n (stateAtom (n + 1) (c₁ (n + 1)) ⋏ stateAtom (n + 1) (c₂ (n + 1))) = 0 ∧
      gapHistory δ n (stateAtom (n + 1) (c₂ (n + 1)) ⋏ stateAtom (n + 1) (c₁ (n + 1))) = 0 := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩ := gapWorld_payout_state n
  constructor
  · simp only [gapHistory, Fin.sum_univ_four, payout_and, a0, a1, a2, a3, b0, b1, b2, b3]; ring
  · simp only [gapHistory, Fin.sum_univ_four, payout_and, a0, a1, a2, a3, b0, b1, b2, b3]; ring

lemma gapSystem_val₁ (n : ℕ) (φ : Sentence) :
    gapSystem.val (n + 1) (c₁ (n + 1)) φ =
      (1 / 2 : ℝ) * (gapWorld n 0).payout φ + (1 / 2 : ℝ) * (gapWorld n 1).payout φ := by
  simp [gapSystem, gapTable]

lemma gapSystem_val₂ (n : ℕ) (φ : Sentence) :
    gapSystem.val (n + 1) (c₂ (n + 1)) φ =
      (1 / 2 : ℝ) * (gapWorld n 2).payout φ + (1 / 2 : ℝ) * (gapWorld n 3).payout φ := by
  simp [gapSystem, gapTable, (c₁_ne_c₂ (n + 1)).symm]

/-! ## The constraints -/

lemma gapHistory_E3 : E3 gapSystem (gapHistory δ) := by
  intro n m o hnm hmo q₁ _ q₂ _ φ _
  have ho : o ≠ n + 1 := by omega
  rw [gapHistory_and_two_ne ho, gapHistory_two_ne ho, mul_zero]

lemma gapHistory_E5 : E5 gapSystem (gapHistory δ) := by
  intro n
  obtain ⟨m1, m2⟩ := gapHistory_state (δ := δ) n
  obtain ⟨e1, e2⟩ := gapHistory_excl (δ := δ) n
  constructor
  · rw [gapSystem_states, Finset.sum_pair (c₁_ne_c₂ _), m1, m2]; norm_num
  · intro q₁ hq₁ q₂ hq₂ hne
    rw [gapSystem_states, Finset.mem_insert, Finset.mem_singleton] at hq₁ hq₂
    rcases hq₁ with rfl | rfl <;> rcases hq₂ with rfl | rfl
    · exact absurd rfl hne
    · exact e1
    · exact e2
    · exact absurd rfl hne

/-- `E4`: on day `0` every day-`0` small sentence is atom-free (`sizeBound 0 = 2`), so the skew
cancels; on later days there is no skew. -/
lemma gapHistory_E4 : E4 gapSystem (gapHistory δ) := by
  intro n φ hφ
  obtain ⟨m1, m2⟩ := gapHistory_state (δ := δ) n
  rw [gapSystem_states, Finset.sum_pair (c₁_ne_c₂ _), m1, m2, gapSystem_val₁, gapSystem_val₂]
  simp only [gapHistory, Fin.sum_univ_four, gapWeight]
  by_cases hn : n = 0
  · subst hn
    have hs : tokenSize φ ≤ 2 := by
      have := mem_smallSet.mp hφ
      unfold SmallOn at this
      have h2 : sizeBound 0 = 2 := by norm_num [sizeBound]
      omega
    have hfree := atomFree_of_tokenSize_le_two φ hs
    rw [payout_congr_of_atomFree hfree (gapWorld 0 1) (gapWorld 0 0),
      payout_congr_of_atomFree hfree (gapWorld 0 2) (gapWorld 0 0),
      payout_congr_of_atomFree hfree (gapWorld 0 3) (gapWorld 0 0)]
    simp only [gapSkew, if_true]; ring
  · simp only [gapSkew, hn, if_false]; ring

/-- Constraint 2 on **every** sentence on every day `n ≥ 1` (no skew there). -/
lemma gapHistory_cond2_pos (n : ℕ) (hn : n ≠ 0) (q : ℕ) (hq : q ∈ gapSystem.states (n + 1))
    (φ : Sentence) :
    gapHistory δ n (φ ⋏ stateAtom (n + 1) q) =
      gapSystem.val (n + 1) q φ * gapHistory δ n (stateAtom (n + 1) q) := by
  rw [gapSystem_states, Finset.mem_insert, Finset.mem_singleton] at hq
  obtain ⟨hJ1, hJ2⟩ := gapHistory_and_state (δ := δ) n φ
  obtain ⟨hM1, hM2⟩ := gapHistory_state (δ := δ) n
  rcases hq with rfl | rfl
  · rw [hJ1, hM1, gapSystem_val₁]; simp only [gapSkew, hn, if_false, gapWeight]; ring
  · rw [hJ2, hM2, gapSystem_val₂]; simp only [gapSkew, hn, if_false, gapWeight]; ring

/-- Faith in the marginal for a two-state system with masses `½`, from the two shapes it can take. -/
lemma faith_pair (v₁ v₂ J₁ J₂ x : ℝ)
    (h : (v₁ = v₂ → J₁ + J₂ = v₁) ∧ (v₁ ≠ v₂ → J₁ = v₁ * (1 / 2) ∧ J₂ = v₂ * (1 / 2))) :
    (if v₁ = x then J₁ else 0) + (if v₂ = x then J₂ else 0) =
      x * ((if v₁ = x then (1 / 2 : ℝ) else 0) + (if v₂ = x then (1 / 2 : ℝ) else 0)) := by
  by_cases h12 : v₁ = v₂
  · have hs := h.1 h12
    subst h12
    by_cases hx : v₁ = x
    · subst hx; simp; linarith
    · simp [hx]
  · obtain ⟨a, b⟩ := h.2 h12
    by_cases hx₁ : v₁ = x <;> by_cases hx₂ : v₂ = x
    · exact absurd (hx₁.trans hx₂.symm) h12
    · subst hx₁; simp [hx₂]; linarith
    · subst hx₂; simp [hx₁]; linarith
    · simp [hx₁, hx₂]

/-- **Faith at `(0, 1)` on all of `Sminus 1 1`**: every sentence there is atom-free or one atom,
and on those the skew on `b` is invisible (the tables agree at `b`, and the skewed joints still
sum to the common value). -/
lemma gapHistory_faith_zero (φ : Sentence) (hφ : φ ∈ Sminus 1 1) (x : ℝ) :
    marginalJoint gapSystem (gapHistory δ) 0 1 φ x =
      x * marginalMass gapSystem (gapHistory δ) 0 1 φ x := by
  unfold marginalJoint marginalMass
  rw [Finset.sum_filter, Finset.sum_filter, gapSystem_states, Finset.sum_pair (c₁_ne_c₂ 1),
    Finset.sum_pair (c₁_ne_c₂ 1)]
  have hJ := gapHistory_and_state (δ := δ) 0 φ
  have hM := gapHistory_state (δ := δ) 0
  have hv₁ := gapSystem_val₁ 0 φ
  have hv₂ := gapSystem_val₂ 0 φ
  simp only [Nat.zero_add] at hJ hM hv₁ hv₂
  rw [hJ.1, hJ.2, hM.1, hM.2, hv₁, hv₂]
  simp only [gapSkew, if_true, gapWeight]
  obtain ⟨hsmall, hday⟩ := mem_Sminus.mp hφ
  have hs : tokenSize φ ≤ 4 := by
    unfold SmallOn at hsmall
    have h4 : sizeBound 1 = 4 := by norm_num [sizeBound]
    omega
  rcases shape_of_tokenSize_le_four φ hs with hfree | ⟨a, rfl⟩
  · rw [payout_congr_of_atomFree hfree (gapWorld 0 1) (gapWorld 0 0),
      payout_congr_of_atomFree hfree (gapWorld 0 2) (gapWorld 0 0),
      payout_congr_of_atomFree hfree (gapWorld 0 3) (gapWorld 0 0)]
    apply faith_pair
    refine ⟨fun _ => by ring, fun h => absurd (by ring) h⟩
  · by_cases ha0 : a = 0
    · subst ha0
      obtain ⟨p0, p1, p2, p3⟩ := gapWorld_payout_cohAtom 0
      simp only [cohAtom] at p0 p1 p2 p3
      rw [p0, p1, p2, p3]
      apply faith_pair
      refine ⟨fun h => by norm_num at h, fun _ => ⟨by ring, by ring⟩⟩
    · by_cases ha1 : a = 1
      · subst ha1
        obtain ⟨p0, p1, p2, p3⟩ := gapWorld_payout_gapAtom 0
        simp only [gapAtom] at p0 p1 p2 p3
        rw [p0, p1, p2, p3]
        apply faith_pair
        refine ⟨fun _ => by ring, fun h => absurd (by ring) h⟩
      · have hd : atomDay a < 0 + 1 := hday a (by simp)
        have p := fun k => gapWorld_payout_atom_other (n := 0) ha0 ha1 hd k
        rw [p 0, p 1, p 2, p 3]
        apply faith_pair
        refine ⟨fun _ => by ring, fun h => absurd (by ring) h⟩

/-- **`FaithMarginal` on the full scope.** -/
theorem gapHistory_faithMarginal : FaithMarginal gapSystem (gapHistory δ) := by
  intro n m hnm φ hφ x
  by_cases hm : m = n + 1
  · subst hm
    by_cases hn : n = 0
    · subst hn
      exact gapHistory_faith_zero φ hφ x
    · unfold marginalJoint marginalMass
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [Finset.mem_filter] at hq
      rw [gapHistory_cond2_pos n hn q hq.1 φ, hq.2]
  · unfold marginalJoint marginalMass
    rw [Finset.sum_eq_zero fun q _ => gapHistory_and_stateAtom_ne hm q φ,
      Finset.sum_eq_zero fun q _ => gapHistory_stateAtom_ne hm q, mul_zero]

/-- **`E2x` fails** at `(0, 1, c₁ 1, atom 1)`: `¼ + δ ≠ ½ · ½`. -/
lemma gapHistory_not_E2x (hδ : δ ≠ 0) : ¬ E2x gapSystem (gapHistory δ) := by
  intro hE2
  have hq : c₁ 1 ∈ gapSystem.states 1 := by rw [gapSystem_states]; simp
  have := hE2 0 1 (by norm_num) _ hq gapAtom gapAtom_mem_Sminus
  have hJ := (gapHistory_and_state (δ := δ) 0 gapAtom).1
  have hM := (gapHistory_state (δ := δ) 0).1
  have hv := gapSystem_val₁ 0 gapAtom
  simp only [Nat.zero_add] at hJ hM hv
  rw [hJ, hM, hv] at this
  obtain ⟨p0, p1, -, -⟩ := gapWorld_payout_gapAtom 0
  rw [p0, p1] at this
  simp only [gapSkew, if_true, gapWeight] at this
  apply hδ; linarith

/-! ## Coherence and distinctness -/

lemma gapHistory_coherent (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 4) (n : ℕ) (A : Finset ℕ) :
    CoherentOn ∅ A (gapHistory δ n) := by
  refine ⟨4, gapWorld n, gapWeight (gapSkew δ n), fun i φ h => by simp at h, ?_, ?_,
    fun φ _ => rfl⟩
  · have hs : 0 ≤ gapSkew δ n ∧ gapSkew δ n ≤ 1 / 4 := by
      unfold gapSkew; split_ifs <;> constructor <;> linarith
    intro i; fin_cases i <;> simp [gapWeight] <;> linarith [hs.1, hs.2]
  · rw [Fin.sum_univ_four]; simp [gapWeight]; ring

lemma gapTable_coherent (m q : ℕ) (A : Finset ℕ) : CoherentOn ∅ A (gapSystem.val m q) := by
  by_cases hq : q = c₁ m
  · refine ⟨2, ![gapWorld (m - 1) 0, gapWorld (m - 1) 1], ![1 / 2, 1 / 2],
      fun i φ h => by simp at h, ?_, ?_, fun φ _ => ?_⟩
    · intro i; fin_cases i <;> norm_num
    · simp [Fin.sum_univ_two]; norm_num
    · simp [gapSystem, gapTable, hq, Fin.sum_univ_two]
  · refine ⟨2, ![gapWorld (m - 1) 2, gapWorld (m - 1) 3], ![1 / 2, 1 / 2],
      fun i φ h => by simp at h, ?_, ?_, fun φ _ => ?_⟩
    · intro i; fin_cases i <;> norm_num
    · simp [Fin.sum_univ_two]; norm_num
    · simp [gapSystem, gapTable, hq, Fin.sum_univ_two]

/-- The two tables of every day differ at `cohAtom` (`1` vs `0`). -/
lemma gapSystem_distinct (m : ℕ) :
    ∀ q ∈ gapSystem.states m, ∀ q' ∈ gapSystem.states m, q ≠ q' →
      gapSystem.val m q ≠ gapSystem.val m q' := by
  have hc : gapSystem.val m (c₁ m) cohAtom = 1 ∧ gapSystem.val m (c₂ m) cohAtom = 0 := by
    obtain ⟨p0, p1, p2, p3⟩ := gapWorld_payout_cohAtom (m - 1)
    constructor
    · simp [gapSystem, gapTable, p0, p1]; norm_num
    · simp [gapSystem, gapTable, (c₁_ne_c₂ m).symm, p2, p3]
  intro q hq q' hq' hne heq
  rw [gapSystem_states, Finset.mem_insert, Finset.mem_singleton] at hq hq'
  have := congrFun heq cohAtom
  rcases hq with rfl | rfl <;> rcases hq' with rfl | rfl
  · exact hne rfl
  · rw [hc.1, hc.2] at this; norm_num at this
  · rw [hc.1, hc.2] at this; norm_num at this
  · exact hne rfl

/-! ## The claim -/

/-- **Two distinct coherent tables, faith in the marginal as defined, no faith in the state.**
Same shape as `TriState.faithMarginal_coherent_distinct_not_imp_e2x`, with two states. -/
theorem two_state_distinct_coherent_gap (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 4) :
    ∃ (S : StateSystem) (Q P : History),
      (∀ n A, CoherentOn ∅ A (P n)) ∧ (∀ n A, CoherentOn ∅ A (Q n)) ∧
      (∀ m q A, CoherentOn ∅ A (S.val m q)) ∧
      (∀ m, ∀ q ∈ S.states m, ∀ q' ∈ S.states m, q ≠ q' → S.val m q ≠ S.val m q') ∧
      (∀ m, (S.states m).card = 2) ∧
      E1x Q P ∧ E3 S P ∧ E4 S P ∧ E5 S P ∧ FaithMarginal S P ∧ ¬ E2x S P := by
  have hc := gapHistory_coherent (δ := δ) hδ.le hδ'.le
  exact ⟨gapSystem, gapHistory δ, gapHistory δ, hc, hc, gapTable_coherent, gapSystem_distinct,
    fun m => by rw [gapSystem_states, Finset.card_pair (c₁_ne_c₂ m)],
    fun _ _ _ => rfl, gapHistory_E3, gapHistory_E4, gapHistory_E5, gapHistory_faithMarginal,
    gapHistory_not_E2x hδ.ne'⟩

/-- **Where the witness lives**: faith in the marginal fails at `a ⋏ b` — a sentence outside
`Sminus 1 1` — exactly as `Pinning.two_state_pinning_scope` predicts for a `⋏`-closed scope. -/
theorem gap_faith_fails_outside_scope (hδ : δ ≠ 0) :
    ¬ ∀ x, marginalJoint gapSystem (gapHistory δ) 0 1 (cohAtom ⋏ gapAtom) x =
      x * marginalMass gapSystem (gapHistory δ) 0 1 (cohAtom ⋏ gapAtom) x := by
  intro h
  have := h (1 / 2)
  unfold marginalJoint marginalMass at this
  rw [Finset.sum_filter, Finset.sum_filter, gapSystem_states, Finset.sum_pair (c₁_ne_c₂ 1),
    Finset.sum_pair (c₁_ne_c₂ 1)] at this
  have hJ := gapHistory_and_state (δ := δ) 0 (cohAtom ⋏ gapAtom)
  have hM := gapHistory_state (δ := δ) 0
  have hv₁ := gapSystem_val₁ 0 (cohAtom ⋏ gapAtom)
  have hv₂ := gapSystem_val₂ 0 (cohAtom ⋏ gapAtom)
  simp only [Nat.zero_add] at hJ hM hv₁ hv₂
  rw [hJ.1, hJ.2, hM.1, hM.2, hv₁, hv₂] at this
  obtain ⟨a0, a1, a2, a3⟩ := gapWorld_payout_cohAtom 0
  obtain ⟨b0, b1, b2, b3⟩ := gapWorld_payout_gapAtom 0
  simp only [payout_and, a0, a1, a2, a3, b0, b1, b2, b3, gapSkew, if_true, gapWeight] at this
  norm_num at this
  apply hδ; linarith

end

end Cleanroom.Bli.BliTrajectory.AuditR3
