/-
# Assessment processes and the live-world Budgeter

Logical Induction's construction reads its deductive process at exactly two
places inside `Budgeter`: the shutoff test and the scaling infimum.  Both consume
the same thing — a finite list of the payout tables that plausible worlds realise
on the finitely many sentences traded so far.  This file makes that list the
primitive.

An `AssessmentProcess` carries a family of world sets `Live n` together with, for
each date and each finite sentence support, a finite list of payout tables that
is **sound** (every listed table is realised by a live world) and **complete**
(every live world realises a listed table), plus **support-local nesting**: a
world live at `n+1` is matched on any finite support by a world live at `n`.

Three things are deliberately *not* hypotheses.

* Nonemptiness. It is not used: the scaling infimum over an empty list is `1`,
  and every conclusion quantified over live worlds is vacuous.  What
  nonemptiness buys is nonvacuity of the criterion, not the lift.
* Global nesting `Live (n+1) ⊆ Live n`. Only its support-local shadow is used, and
  that is strictly weaker: `lateAllTrueLive_not_globally_nested` satisfies the whole
  interface with `Live 1 ⊆ Live 0` false.  The two coincide exactly for families
  determined by their finite restrictions — `live_subset_of_finiteDetermined` — which
  is what `PC(D_n)` is.
* Computability. The Budgeter lemmas need the restriction lists to be finite, not
  to be computable; computability is what makes the market a program and is
  tracked separately.

Names are provisional (`AGENTS.md` standard 6).  Logical Induction's own results
are used as the pinned dependency's theorems, not restated as axioms.
-/

import LogicalInduction.Construction.TradingFirm

namespace Workspace.Normativity.Contrib.AssessmentProcess

open LogicalInduction
open Classical

/-! ## Payout tables

A world is consumed by a strategy only through its `{0,1}` payouts on the
sentences the strategy trades.  `ratPayout` is that reading, and `PayoutAgrees`
is the only relation between a table and a world any of the lemmas below need. -/

/-- The exact rational `{0,1}` payout table of a propositionally consistent world. -/
noncomputable def ratPayout (v : PCWorld) : Sentence → ℚ :=
  fun φ => if v.Holds φ then 1 else 0

lemma payout_eq_ratPayout (v : PCWorld) (φ : Sentence) :
    v.payout φ = (ratPayout v φ : ℝ) := by
  unfold ratPayout PCWorld.payout
  by_cases h : v.Holds φ <;> simp [h]

/-- A table agrees with a world on a finite support. -/
def PayoutAgrees (S : Finset Sentence) (w : Sentence → ℚ) (v : PCWorld) : Prop :=
  ∀ φ ∈ S, w φ = ratPayout v φ

lemma PayoutAgrees.mono {S S' : Finset Sentence} {w : Sentence → ℚ} {v : PCWorld}
    (h : PayoutAgrees S w v) (hS : S' ⊆ S) : PayoutAgrees S' w v :=
  fun φ hφ => h φ (hS hφ)

/-- The sentences a trader has taken a position on through day `n`. -/
def supportUpTo (Tr : Trader) (n : ℕ) : Finset Sentence :=
  (Finset.range (n + 1)).biUnion fun i => (Tr.strat i).support

lemma support_subset_supportUpTo (Tr : Trader) {i n : ℕ} (hi : i ≤ n) :
    (Tr.strat i).support ⊆ supportUpTo Tr n := by
  intro φ hφ
  exact Finset.mem_biUnion.mpr ⟨i, by simp; omega, hφ⟩

lemma supportUpTo_mono (Tr : Trader) {m n : ℕ} (h : m ≤ n) :
    supportUpTo Tr m ⊆ supportUpTo Tr n := by
  intro φ hφ
  obtain ⟨i, hi, hφi⟩ := Finset.mem_biUnion.mp hφ
  simp only [Finset.mem_range] at hi
  exact Finset.mem_biUnion.mpr ⟨i, by simp; omega, hφi⟩

/-! ## The interface -/

/-- An **assessment process**: a family of world sets together with a finite,
sound and complete enumeration of the payout tables its worlds realise on any
finite sentence support, and support-local temporal nesting.

`Live` is the semantic object the criterion is stated over; `restrict` is the
only thing the construction ever touches. -/
structure Assessment where
  /-- The worlds a trader's net worth is assessed in at date `n`. -/
  Live : ℕ → PCWorld → Prop
  /-- The finite list of payout tables realised on a finite support at date `n`. -/
  tables : ℕ → Finset Sentence → List (Sentence → ℚ)
  /-- Soundness: every listed table is realised by a world live at that date. -/
  tables_sound : ∀ (n : ℕ) (S : Finset Sentence) (w : Sentence → ℚ),
    w ∈ tables n S → ∃ v : PCWorld, Live n v ∧ PayoutAgrees S w v
  /-- Completeness: every live world's restriction is listed. -/
  tables_complete : ∀ (n : ℕ) (S : Finset Sentence) (v : PCWorld), Live n v →
    ∃ w ∈ tables n S, PayoutAgrees S w v
  /-- Support-local nesting: on any finite support, a world live at `n+1` is
  matched by a world live at `n`. -/
  nested : ∀ (n : ℕ) (S : Finset Sentence) (v : PCWorld), Live (n + 1) v →
    ∃ v' : PCWorld, Live n v' ∧ ∀ φ ∈ S, ratPayout v' φ = ratPayout v φ

namespace Assessment

private lemma nested_add (L : Assessment) (S : Finset Sentence) :
    ∀ (k m : ℕ) (v : PCWorld), L.Live (m + k) v →
      ∃ v', L.Live m v' ∧ ∀ φ ∈ S, ratPayout v' φ = ratPayout v φ := by
  intro k
  induction k with
  | zero => intro m v hv; exact ⟨v, by simpa using hv, fun _ _ => rfl⟩
  | succ k ih =>
      intro m v hv
      obtain ⟨v₁, hv₁, hagree₁⟩ := L.nested (m + k) S v hv
      obtain ⟨v₂, hv₂, hagree₂⟩ := ih m v₁ hv₁
      exact ⟨v₂, hv₂, fun φ hφ => (hagree₂ φ hφ).trans (hagree₁ φ hφ)⟩

/-- Support-local nesting at arbitrary distance. -/
lemma nested_le (L : Assessment) {m n : ℕ} (h : m ≤ n) (S : Finset Sentence)
    {v : PCWorld} (hv : L.Live n v) :
    ∃ v', L.Live m v' ∧ ∀ φ ∈ S, ratPayout v' φ = ratPayout v φ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact L.nested_add S k m v hv

/-! ## The generalized criterion -/

/-- The plausible assessments of `Tr`'s net worth relative to an assessment
process: the same shape as `def:exploitation` with `PC(D n)` replaced. -/
def plausibleAssessments (L : Assessment) (Tr : Trader) (V : History) : Set ℝ :=
  { x | ∃ (n : ℕ) (v : PCWorld), L.Live n v ∧ x = Tr.netWorth V v n }

/-- `Tr` **exploits** `V` relative to `L`: bounded downside, unbounded upside,
assessed in the live worlds. -/
def Exploits (L : Assessment) (Tr : Trader) (V : History) : Prop :=
  BddBelow (L.plausibleAssessments Tr V) ∧ ¬ BddAbove (L.plausibleAssessments Tr V)

/-- The generalized Logical Induction Criterion `LIC_L`. -/
def IsLogicalInductor (L : Assessment) (P : History) : Prop :=
  ComputableMarket P ∧ ∀ Tr : Trader, EfficientlyComputable Tr → ¬ L.Exploits Tr P

end Assessment

/-! ## The deductive instance

`PC(D n)` is an assessment process, with `restrict` supplied by the source's own
finite atom enumeration read through the traded support. -/

/-- The payout table a Boolean atom assignment induces. -/
lemma boolPayoutRat_eq_ratPayout (u : ℕ → Bool) (φ : Sentence) :
    boolPayoutRat u φ = ratPayout (boolPCWorld u) φ := by
  unfold boolPayoutRat ratPayout
  by_cases h : sentenceBool u φ = true
  · simp [h, (sentenceBool_eq_true_iff u φ).mp h]
  · have hw : ¬ (boolPCWorld u).Holds φ := fun hv =>
      h ((sentenceBool_eq_true_iff u φ).mpr hv)
    cases hs : sentenceBool u φ <;> simp_all

/-- The atom context sufficient to decide the stage and evaluate a support. -/
def deductiveContext (D : Finset Sentence) (S : Finset Sentence) : Finset ℕ :=
  D.biUnion Sentence.atoms ∪ S.biUnion Sentence.atoms

/-- The finite enumeration of payout tables the deductive process realises. -/
def deductiveRestrict (DP : DeductiveProcess) (n : ℕ) (S : Finset Sentence) :
    List (Sentence → ℚ) :=
  let A := deductiveContext (DP.D n) S
  ((finiteAtomAssignments A).filter fun bits =>
      tableConsistent (finiteAtomTable A bits) (DP.D n)).map fun bits =>
    boolPayoutRat (finiteAtomTable A bits)

lemma deductiveRestrict_sound (DP : DeductiveProcess) (n : ℕ) (S : Finset Sentence)
    (w : Sentence → ℚ) (hw : w ∈ deductiveRestrict DP n S) :
    ∃ v, v.ConsistentWith (DP.D n) ∧ PayoutAgrees S w v := by
  simp only [deductiveRestrict, List.mem_map, List.mem_filter] at hw
  obtain ⟨bits, ⟨_, hcons⟩, rfl⟩ := hw
  refine ⟨boolPCWorld (finiteAtomTable (deductiveContext (DP.D n) S) bits), ?_, ?_⟩
  · exact (tableConsistent_eq_true_iff _ (DP.D n)).mp hcons
  · intro φ _
    exact boolPayoutRat_eq_ratPayout _ φ

lemma deductiveRestrict_complete (DP : DeductiveProcess) (n : ℕ)
    (S : Finset Sentence) (v : PCWorld) (hv : v.ConsistentWith (DP.D n)) :
    ∃ w ∈ deductiveRestrict DP n S, PayoutAgrees S w v := by
  set A := deductiveContext (DP.D n) S with hA
  refine ⟨boolPayoutRat (finiteAtomTable A (restrictedAssignment A v)), ?_, ?_⟩
  · simp only [deductiveRestrict, List.mem_map, List.mem_filter]
    refine ⟨restrictedAssignment A v, ⟨restrictedAssignment_mem A v, ?_⟩, rfl⟩
    apply (tableConsistent_eq_true_iff _ (DP.D n)).mpr
    intro φ hφ
    apply (sentenceBool_eq_true_iff _ φ).mp
    apply (sentenceBool_restricted_world A v φ ?_).mpr (hv φ hφ)
    intro a ha
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨φ, hφ, ha⟩)
  · intro φ hφ
    have hsub : φ.atoms ⊆ A := by
      intro a ha
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨φ, hφ, ha⟩)
    unfold boolPayoutRat ratPayout
    by_cases hv' : v.Holds φ
    · simp [(sentenceBool_restricted_world A v φ hsub).mpr hv', hv']
    · have : sentenceBool (finiteAtomTable A (restrictedAssignment A v)) φ ≠ true :=
        fun h => hv' ((sentenceBool_restricted_world A v φ hsub).mp h)
      simp [this, hv']

/-- The assessment process of a deductive process: `Live n = PC(D n)`. -/
def ofDeductiveProcess (DP : DeductiveProcess) : Assessment where
  Live n v := v.ConsistentWith (DP.D n)
  tables := deductiveRestrict DP
  tables_sound := deductiveRestrict_sound DP
  tables_complete := deductiveRestrict_complete DP
  nested n S v hv := ⟨v, fun φ hφ => hv φ (DP.mono n hφ), fun _ _ => rfl⟩

@[simp] lemma ofDeductiveProcess_live (DP : DeductiveProcess) (n : ℕ) (v : PCWorld) :
    (ofDeductiveProcess DP).Live n v ↔ v.ConsistentWith (DP.D n) := Iff.rfl

/-- **Criterion recovery.** Exploitation relative to the deductive assessment
process is exploitation relative to the deductive process, on the nose. -/
theorem exploits_ofDeductiveProcess (DP : DeductiveProcess) (Tr : Trader)
    (V : History) :
    (ofDeductiveProcess DP).Exploits Tr V ↔ Tr.Exploits V DP := by
  have hset : (ofDeductiveProcess DP).plausibleAssessments Tr V =
      Tr.plausibleAssessments V DP := rfl
  unfold Assessment.Exploits Trader.Exploits
  rw [hset]

/-! ## Net worth is a function of the traded restrictions

The one structural fact the whole lift turns on: a trader's net worth through day
`n` reads a world only through its payouts on the finitely many sentences the
trader has traded.  Two worlds agreeing there are interchangeable. -/

lemma netWorth_congr_on_support (T : Trader) (P : History) (n : ℕ)
    {S : Finset Sentence} {v v' : PCWorld}
    (hS : ∀ i, i ≤ n → (T.strat i).support ⊆ S)
    (hagree : ∀ φ ∈ S, ratPayout v' φ = ratPayout v φ) :
    T.netWorth P v' n = T.netWorth P v n := by
  unfold Trader.netWorth
  apply Finset.sum_congr rfl
  intro i hi
  apply (T.strat i).value_congr_payout P
  intro p hp
  have hmem : p.2 ∈ S :=
    hS i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) ((T.strat i).snd_mem_support hp)
  rw [payout_eq_ratPayout v' p.2, payout_eq_ratPayout v p.2, hagree p.2 hmem]

/-! ## The generalized Budgeter

Every definition below is the source's, with the Boolean atom table `u` replaced
by a rational payout table `w` and the finite plausible-world enumeration replaced
by `L.tables`.  Nothing else changes. -/

/-- The day-`n` value of a strategy at a fixed payout table, reified as a feature
of the market history.  Source: `Strategy.worldValueFeature`. -/
def worldValueFeatureOf {n : ℕ} (T : Strategy n) (w : Sentence → ℚ) : EF :=
  ROIBudget.sumFeatures (T.trades.map fun p =>
    .mul p.1 (.add (.const (w p.2)) (.mul (.const (-1)) (.price p.2 n))))

lemma worldValueFeatureOf_rank_le {n : ℕ} (T : Strategy n) (w : Sentence → ℚ) :
    (worldValueFeatureOf T w).rank ≤ n := by
  apply ROIBudget.sumFeatures_rank_le
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨p, hp, rfl⟩ := he
  simp only [EF.rank_mul, EF.rank_add, EF.rank_const, EF.rank_price]
  exact max_le (T.rank_le p hp) (max_le (by omega) (max_le (by omega) (by omega)))

lemma worldValueFeatureOf_denote {n : ℕ} (T : Strategy n) (w : Sentence → ℚ)
    (P : History) :
    (worldValueFeatureOf T w).denote P = T.value P (fun φ => (w φ : ℝ)) := by
  rw [worldValueFeatureOf, ROIBudget.sumFeatures_denote]
  unfold Strategy.value
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply, EF.denote_mul, EF.denote_add, EF.denote_const,
    EF.denote_price, Pi.mul_apply, Pi.add_apply]
  have hneg : ((-1 : ℚ) : ℝ) = -1 := by norm_num
  rw [hneg]
  ring

/-- A payout table that agrees with a world on the traded support gives the
strategy the same value as the world does. -/
lemma value_eq_of_payoutAgrees {n : ℕ} (T : Strategy n) (P : History)
    {S : Finset Sentence} {w : Sentence → ℚ} {v : PCWorld}
    (hS : T.support ⊆ S) (hw : PayoutAgrees S w v) :
    T.value P (fun φ => (w φ : ℝ)) = T.value P v.payout := by
  apply T.value_congr_payout P
  intro p hp
  rw [hw p.2 (hS (T.snd_mem_support hp)), ← payout_eq_ratPayout]

/-- Raw wealth strictly before day `n`, at a payout table. -/
def rawPriorWorthOf (Tr : Trader) (Q : ℕ → Sentence → ℚ) (w : Sentence → ℚ)
    (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (Tr.strat i).marketValueRat Q w

/-- Raw wealth through day `m`, at a payout table. -/
def rawWorthOf (Tr : Trader) (Q : ℕ → Sentence → ℚ) (w : Sentence → ℚ)
    (m : ℕ) : ℚ :=
  rawPriorWorthOf Tr Q w (m + 1)

lemma rawPriorWorthOf_eq_of_eq_prefix (Tr : Trader) (Q R : ℕ → Sentence → ℚ)
    (w : Sentence → ℚ) (n : ℕ)
    (hQR : ∀ day, day < n → ∀ φ, Q day φ = R day φ) :
    rawPriorWorthOf Tr Q w n = rawPriorWorthOf Tr R w n := by
  unfold rawPriorWorthOf
  apply Finset.sum_congr rfl
  intro i hi
  apply (Tr.strat i).marketValueRat_eq_of_eqUpTo
  intro day hday φ
  exact hQR day (lt_of_le_of_lt hday (Finset.mem_range.mp hi)) φ

/-- The rational prior wealth at a payout table is the sum of the real day values
at that table.  Prefix form: no rational quote for the still-variable day `n`. -/
lemma rawPriorWorthOf_cast_sum (Tr : Trader) (P : History) (Q : ℕ → Sentence → ℚ)
    (w : Sentence → ℚ) (n : ℕ)
    (hQ : ∀ day, day < n → ∀ φ, P day φ = (Q day φ : ℝ)) :
    (rawPriorWorthOf Tr Q w n : ℝ) =
      ∑ i ∈ Finset.range n, (Tr.strat i).value P (fun φ => (w φ : ℝ)) := by
  rw [rawPriorWorthOf, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  have hstep : (Tr.strat i).value (fun day φ => ((Q day φ : ℚ) : ℝ))
      (fun φ => (w φ : ℝ)) = ((Tr.strat i).marketValueRat Q w : ℝ) :=
    (Tr.strat i).value_eq_marketRatCast (fun day φ => ((Q day φ : ℚ) : ℝ)) Q
      (fun _ _ => rfl) (fun φ => (w φ : ℝ)) w (fun _ => rfl)
  have hshift : (Tr.strat i).value P (fun φ => (w φ : ℝ)) =
      (Tr.strat i).value (fun day φ => ((Q day φ : ℚ) : ℝ)) (fun φ => (w φ : ℝ)) := by
    apply Strategy.value_eq_of_eqUpTo
    intro day hday φ
    exact hQ day (lt_of_le_of_lt hday hin) φ
  rw [hshift, hstep]

/-- The rational prior wealth at a table agreeing with a live world is that
world's real prior net worth. -/
lemma rawPriorWorthOf_cast (Tr : Trader) (P : History) (Q : ℕ → Sentence → ℚ)
    (n : ℕ) (hQ : ∀ day, day < n → ∀ φ, P day φ = (Q day φ : ℝ))
    {S : Finset Sentence} {w : Sentence → ℚ} {v : PCWorld}
    (hS : ∀ i, i < n → (Tr.strat i).support ⊆ S) (hw : PayoutAgrees S w v) :
    (rawPriorWorthOf Tr Q w n : ℝ) = Tr.priorNetWorth P v n := by
  rw [rawPriorWorthOf_cast_sum Tr P Q w n hQ, Trader.priorNetWorth]
  apply Finset.sum_congr rfl
  intro i hi
  exact value_eq_of_payoutAgrees (Tr.strat i) P (hS i (Finset.mem_range.mp hi)) hw

lemma rawWorthOf_cast (Tr : Trader) (P : History) (Q : ℕ → Sentence → ℚ)
    (m : ℕ) (hQ : ∀ day, day ≤ m → ∀ φ, P day φ = (Q day φ : ℝ))
    {S : Finset Sentence} {w : Sentence → ℚ} {v : PCWorld}
    (hS : ∀ i, i ≤ m → (Tr.strat i).support ⊆ S) (hw : PayoutAgrees S w v) :
    (rawWorthOf Tr Q w m : ℝ) = Tr.netWorth P v m := by
  rw [rawWorthOf, rawPriorWorthOf_cast Tr P Q (m + 1)
    (fun day hday φ => hQ day (by omega) φ)
    (fun i hi => hS i (by omega)) hw]
  rfl

/-- One world-specific reciprocal loss cap, at a payout table.  Source:
`budgetWorldScale`. -/
def budgetWorldScaleOf (Tr : Trader) (b : ℕ) (Q : ℕ → Sentence → ℚ)
    (w : Sentence → ℚ) (n : ℕ) : EF :=
  .safeRecip (.mul
    (.const ((b + rawPriorWorthOf Tr Q w n)⁻¹))
    (EF.neg (worldValueFeatureOf (Tr.strat n) w)))

lemma budgetWorldScaleOf_rank_le (Tr : Trader) (b : ℕ) (Q : ℕ → Sentence → ℚ)
    (w : Sentence → ℚ) (n : ℕ) : (budgetWorldScaleOf Tr b Q w n).rank ≤ n := by
  simp only [budgetWorldScaleOf, EF.neg, EF.rank_safeRecip, EF.rank_mul,
    EF.rank_const, Nat.max_eq_right, Nat.zero_max]
  exact worldValueFeatureOf_rank_le (Tr.strat n) w

lemma budgetWorldScaleOf_denote (Tr : Trader) (b : ℕ) (P : History)
    (Q : ℕ → Sentence → ℚ) (w : Sentence → ℚ) (n : ℕ) :
    (budgetWorldScaleOf Tr b Q w n).denote P =
      lossCap ((b : ℝ) + (rawPriorWorthOf Tr Q w n : ℝ))
        ((Tr.strat n).value P (fun φ => (w φ : ℝ))) := by
  simp only [budgetWorldScaleOf, EF.denote_safeRecip, EF.denote_mul, EF.denote_const,
    Pi.mul_apply, EF.denote_neg, worldValueFeatureOf_denote, lossCap]
  norm_cast
  rw [div_eq_mul_inv]
  congr 2
  rw [Rat.cast_inv]
  ring

lemma budgetWorldScaleOf_eq_of_eq_prefix (Tr : Trader) (b : ℕ)
    (Q R : ℕ → Sentence → ℚ) (w : Sentence → ℚ) (n : ℕ)
    (hQR : ∀ day, day < n → ∀ φ, Q day φ = R day φ) :
    budgetWorldScaleOf Tr b Q w n = budgetWorldScaleOf Tr b R w n := by
  unfold budgetWorldScaleOf
  rw [rawPriorWorthOf_eq_of_eq_prefix Tr Q R w n hQR]

/-- The scaling infimum over the live restrictions at date `n`.  Source:
`budgetScaleFeature`. -/
def budgetScaleFeature (L : Assessment) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) : EF :=
  EF.listMin ((L.tables n (supportUpTo Tr n)).map fun w =>
    budgetWorldScaleOf Tr b Q w n)

/-- The shutoff test: some live restriction at some earlier date shows the raw
trader at or below `-b`.  Source: `priorBudgetBreach`. -/
def priorBudgetBreach (L : Assessment) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) : Bool :=
  (List.range n).any fun m =>
    (L.tables m (supportUpTo Tr m)).any fun w =>
      decide (rawWorthOf Tr Q w m ≤ -(b : ℚ))

lemma budgetScaleFeature_rank_le (L : Assessment) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) :
    (budgetScaleFeature L Tr b Q n).rank ≤ n := by
  unfold budgetScaleFeature
  apply EF.listMin_rank_le
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨w, _, rfl⟩ := he
  exact budgetWorldScaleOf_rank_le Tr b Q w n

lemma budgetScaleFeature_eq_of_eq_prefix (L : Assessment) (Tr : Trader) (b : ℕ)
    (Q R : ℕ → Sentence → ℚ) (n : ℕ)
    (hQR : ∀ day, day < n → ∀ φ, Q day φ = R day φ) :
    budgetScaleFeature L Tr b Q n = budgetScaleFeature L Tr b R n := by
  unfold budgetScaleFeature
  apply congrArg EF.listMin
  apply List.map_congr_left
  intro w _
  exact budgetWorldScaleOf_eq_of_eq_prefix Tr b Q R w n hQR

private lemma priorBudgetBreach_mono_prefix (L : Assessment) (Tr : Trader) (b : ℕ)
    (Q R : ℕ → Sentence → ℚ) (n : ℕ)
    (hQR : ∀ day, day < n → ∀ φ, Q day φ = R day φ)
    (h : priorBudgetBreach L Tr b Q n = true) :
    priorBudgetBreach L Tr b R n = true := by
  unfold priorBudgetBreach at h ⊢
  obtain ⟨m, hm, hinner⟩ := List.any_eq_true.mp h
  obtain ⟨w, hw, hle⟩ := List.any_eq_true.mp hinner
  refine List.any_eq_true.mpr ⟨m, hm, List.any_eq_true.mpr ⟨w, hw, ?_⟩⟩
  have hmn : m < n := List.mem_range.mp hm
  rw [rawWorthOf, rawPriorWorthOf_eq_of_eq_prefix Tr R Q w (m + 1)
    (fun day hday φ => (hQR day (by omega) φ).symm)]
  exact hle

lemma priorBudgetBreach_eq_of_eq_prefix (L : Assessment) (Tr : Trader) (b : ℕ)
    (Q R : ℕ → Sentence → ℚ) (n : ℕ)
    (hQR : ∀ day, day < n → ∀ φ, Q day φ = R day φ) :
    priorBudgetBreach L Tr b Q n = priorBudgetBreach L Tr b R n := by
  cases hQb : priorBudgetBreach L Tr b Q n
  · cases hRb : priorBudgetBreach L Tr b R n
    · rfl
    · have := priorBudgetBreach_mono_prefix L Tr b R Q n
        (fun day hd φ => (hQR day hd φ).symm) hRb
      rw [hQb] at this; exact absurd this (by simp)
  · cases hRb : priorBudgetBreach L Tr b R n
    · have := priorBudgetBreach_mono_prefix L Tr b Q R n hQR hQb
      rw [hRb] at this; exact absurd this (by simp)
    · rfl

lemma budgetScaleFeature_denote_pos (L : Assessment) (Tr : Trader) (b : ℕ)
    (P : History) (Q : ℕ → Sentence → ℚ) (n : ℕ) :
    0 < (budgetScaleFeature L Tr b Q n).denote P := by
  unfold budgetScaleFeature
  apply EF.listMin_denote_pos
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨w, _, rfl⟩ := he
  rw [budgetWorldScaleOf_denote]
  exact lossCap_pos _ _

lemma budgetScaleFeature_denote_le_one (L : Assessment) (Tr : Trader) (b : ℕ)
    (P : History) (Q : ℕ → Sentence → ℚ) (n : ℕ) :
    (budgetScaleFeature L Tr b Q n).denote P ≤ 1 := by
  unfold budgetScaleFeature
  exact EF.listMin_denote_le_one _ P

/-- `def:budgeter` over an assessment process. -/
def BudgeterAt (L : Assessment) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) : Strategy n :=
  if priorBudgetBreach L Tr b Q n then
    ⟨[], by simp⟩
  else
    (Tr.strat n).scaleBy (budgetScaleFeature L Tr b Q n)
      (budgetScaleFeature_rank_le L Tr b Q n)

/-- The Budgeter never trades a sentence the raw trader has not traded. -/
lemma BudgeterAt_support_subset (L : Assessment) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) :
    (BudgeterAt L Tr b Q n).support ⊆ (Tr.strat n).support := by
  unfold BudgeterAt
  by_cases h : priorBudgetBreach L Tr b Q n
  · simp only [h, if_true]
    intro φ hφ
    simp [Strategy.support] at hφ
  · simp only [h, Bool.false_eq_true, if_false]
    intro φ hφ
    simp only [Strategy.support, Strategy.scaleBy, List.toFinset_map, List.mem_toFinset,
      Finset.mem_image, List.mem_map] at hφ ⊢
    obtain ⟨p, hp, rfl⟩ := hφ
    obtain ⟨q, hq, rfl⟩ := hp
    exact ⟨q, hq, rfl⟩

/-- The realized budgeted trader against a fixed rational market table. -/
def budgetedTrader (L : Assessment) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) : Trader where
  strat n := BudgeterAt L Tr b Q n

lemma BudgeterAt_eq_of_eq_prefix (L : Assessment) (Tr : Trader) (b : ℕ)
    (Q R : ℕ → Sentence → ℚ) (n : ℕ)
    (hQR : ∀ day, day < n → ∀ φ, Q day φ = R day φ) :
    BudgeterAt L Tr b Q n = BudgeterAt L Tr b R n := by
  unfold BudgeterAt
  rw [priorBudgetBreach_eq_of_eq_prefix L Tr b Q R n hQR]
  by_cases hbreach : priorBudgetBreach L Tr b R n
  · simp [hbreach]
  · simp only [hbreach, Bool.false_eq_true, if_false]
    have hscale := budgetScaleFeature_eq_of_eq_prefix L Tr b Q R n hQR
    unfold Strategy.scaleBy
    congr 1
    rw [hscale]

/-! ### The shutoff test says what it means -/

lemma priorBudgetBreach_eq_true_iff (L : Assessment) (Tr : Trader) (b : ℕ)
    (P : History) (Q : ℕ → Sentence → ℚ) (n : ℕ)
    (hQ : ∀ day, day < n → ∀ φ, P day φ = (Q day φ : ℝ)) :
    priorBudgetBreach L Tr b Q n = true ↔
      ∃ m, m < n ∧ ∃ v : PCWorld, L.Live m v ∧ Tr.netWorth P v m ≤ -(b : ℝ) := by
  constructor
  · intro h
    obtain ⟨m, hm, hinner⟩ := List.any_eq_true.mp h
    obtain ⟨w, hw, hle⟩ := List.any_eq_true.mp hinner
    have hmn : m < n := List.mem_range.mp hm
    obtain ⟨v, hv, hagree⟩ := L.tables_sound m (supportUpTo Tr m) w hw
    refine ⟨m, hmn, v, hv, ?_⟩
    have hcast : (rawWorthOf Tr Q w m : ℝ) = Tr.netWorth P v m :=
      rawWorthOf_cast Tr P Q m (fun day hday φ => hQ day (by omega) φ)
        (fun i hi => support_subset_supportUpTo Tr hi) hagree
    have hq : rawWorthOf Tr Q w m ≤ -(b : ℚ) := of_decide_eq_true hle
    have : (rawWorthOf Tr Q w m : ℝ) ≤ -(b : ℝ) := by exact_mod_cast hq
    rwa [hcast] at this
  · rintro ⟨m, hmn, v, hv, hle⟩
    obtain ⟨w, hw, hagree⟩ := L.tables_complete m (supportUpTo Tr m) v hv
    have hcast : (rawWorthOf Tr Q w m : ℝ) = Tr.netWorth P v m :=
      rawWorthOf_cast Tr P Q m (fun day hday φ => hQ day (by omega) φ)
        (fun i hi => support_subset_supportUpTo Tr hi) hagree
    have hq : rawWorthOf Tr Q w m ≤ -(b : ℚ) := by
      have : (rawWorthOf Tr Q w m : ℝ) ≤ -(b : ℝ) := by rw [hcast]; exact hle
      exact_mod_cast this
    exact List.any_eq_true.mpr ⟨m, List.mem_range.mpr hmn,
      List.any_eq_true.mpr ⟨w, hw, decide_eq_true hq⟩⟩

lemma priorBudgetBreach_eq_false_iff (L : Assessment) (Tr : Trader) (b : ℕ)
    (P : History) (Q : ℕ → Sentence → ℚ) (n : ℕ)
    (hQ : ∀ day, day < n → ∀ φ, P day φ = (Q day φ : ℝ)) :
    priorBudgetBreach L Tr b Q n = false ↔
      ∀ m, m < n → ∀ v : PCWorld, L.Live m v → -(b : ℝ) < Tr.netWorth P v m := by
  rw [← Bool.not_eq_true, priorBudgetBreach_eq_true_iff L Tr b P Q n hQ]
  constructor
  · intro h m hm v hv
    by_contra hcon
    exact h ⟨m, hm, v, hv, le_of_not_gt hcon⟩
  · rintro h ⟨m, hm, v, hv, hle⟩
    exact absurd (h m hm v hv) (not_lt_of_ge hle)

/-! ### `lem:budgeter` part 1

Support-local nesting is consumed exactly here: the available capital in the
denominator of a world's loss cap is positive because a world live at `n` is
matched, on the traded support, by a world live at `n-1`, where the safety
hypothesis applies. -/

private lemma available_pos (L : Assessment) (Tr : Trader) (b : ℕ) (hb : 0 < b)
    (P : History) (n : ℕ)
    (hsafe : ∀ m, m ≤ n → ∀ v : PCWorld, L.Live m v → -(b : ℝ) < Tr.netWorth P v m)
    (v : PCWorld) (hv : L.Live n v) :
    0 < (b : ℝ) + Tr.priorNetWorth P v n := by
  cases n with
  | zero => simp only [Trader.priorNetWorth, Finset.range_zero, Finset.sum_empty, add_zero]
            exact_mod_cast hb
  | succ m =>
      obtain ⟨v', hv', hagree'⟩ := L.nested m (supportUpTo Tr m) v hv
      have hnet : Tr.netWorth P v' m = Tr.netWorth P v m :=
        netWorth_congr_on_support Tr P m
          (fun i hi => support_subset_supportUpTo Tr hi) hagree'
      have hs := hsafe m (by omega) v' hv'
      rw [hnet] at hs
      change 0 < (b : ℝ) + Tr.netWorth P v m
      linarith

lemma budgetScaleFeature_denote_eq_one_of_safe (L : Assessment) (Tr : Trader)
    (b : ℕ) (hb : 0 < b) (P : History) (Q : ℕ → Sentence → ℚ) (n : ℕ)
    (hQ : ∀ day, day < n → ∀ φ, P day φ = (Q day φ : ℝ))
    (hsafe : ∀ m, m ≤ n → ∀ v : PCWorld, L.Live m v → -(b : ℝ) < Tr.netWorth P v m) :
    (budgetScaleFeature L Tr b Q n).denote P = 1 := by
  unfold budgetScaleFeature
  apply EF.listMin_denote_eq_one
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨w, hw, rfl⟩ := he
  obtain ⟨v, hv, hagree⟩ := L.tables_sound n (supportUpTo Tr n) w hw
  have hcurrent : (Tr.strat n).value P (fun φ => (w φ : ℝ))
      = (Tr.strat n).value P v.payout :=
    value_eq_of_payoutAgrees (Tr.strat n) P
      (support_subset_supportUpTo Tr (le_refl n)) hagree
  have hprior : (rawPriorWorthOf Tr Q w n : ℝ) = Tr.priorNetWorth P v n :=
    rawPriorWorthOf_cast Tr P Q n hQ
      (fun i hi => support_subset_supportUpTo Tr (le_of_lt hi)) hagree
  have havail := available_pos L Tr b hb P n hsafe v hv
  have htotal := hsafe n (le_refl n) v hv
  rw [Tr.netWorth_eq_prior_add] at htotal
  have hloss : -((Tr.strat n).value P v.payout) < (b : ℝ) + Tr.priorNetWorth P v n := by
    linarith
  rw [budgetWorldScaleOf_denote, hcurrent, hprior]
  exact lossCap_eq_one_of_ratio_le ((div_le_one havail).mpr hloss.le)

/-- `lem:budgeter` part 1: on a market where the raw trader stays strictly inside
budget at every live world, the Budgeter reproduces its day-`n` trade exactly. -/
theorem BudgeterAt_value_eq_of_safe (L : Assessment) (Tr : Trader) (b : ℕ)
    (hb : 0 < b) (P : History) (Q : ℕ → Sentence → ℚ) (n : ℕ)
    (hQ : ∀ day, day < n → ∀ φ, P day φ = (Q day φ : ℝ))
    (hsafe : ∀ m, m ≤ n → ∀ v : PCWorld, L.Live m v → -(b : ℝ) < Tr.netWorth P v m)
    (w : Sentence → ℝ) :
    (BudgeterAt L Tr b Q n).value P w = (Tr.strat n).value P w := by
  have hbreach : priorBudgetBreach L Tr b Q n = false :=
    (priorBudgetBreach_eq_false_iff L Tr b P Q n hQ).mpr
      (fun m hm => hsafe m (le_of_lt hm))
  simp only [BudgeterAt, hbreach, Bool.false_eq_true, if_false]
  rw [Strategy.scaleBy_value,
    budgetScaleFeature_denote_eq_one_of_safe L Tr b hb P Q n hQ hsafe, one_mul]

/-! ### `lem:budgeter` part 2 -/

lemma budgetScaleFeature_denote_le_lossCap (L : Assessment) (Tr : Trader) (b : ℕ)
    (P : History) (Q : ℕ → Sentence → ℚ) (n : ℕ)
    (hQ : ∀ day, day < n → ∀ φ, P day φ = (Q day φ : ℝ))
    (v : PCWorld) (hv : L.Live n v) :
    (budgetScaleFeature L Tr b Q n).denote P ≤
      lossCap ((b : ℝ) + Tr.priorNetWorth P v n)
        ((Tr.strat n).value P v.payout) := by
  obtain ⟨w, hw, hagree⟩ := L.tables_complete n (supportUpTo Tr n) v hv
  have hmem : budgetWorldScaleOf Tr b Q w n ∈
      (L.tables n (supportUpTo Tr n)).map fun w => budgetWorldScaleOf Tr b Q w n :=
    List.mem_map.mpr ⟨w, hw, rfl⟩
  have hle := EF.listMin_denote_le_of_mem _ hmem P
  rw [budgetWorldScaleOf_denote] at hle
  have hcurrent : (Tr.strat n).value P (fun φ => (w φ : ℝ))
      = (Tr.strat n).value P v.payout :=
    value_eq_of_payoutAgrees (Tr.strat n) P
      (support_subset_supportUpTo Tr (le_refl n)) hagree
  have hprior : (rawPriorWorthOf Tr Q w n : ℝ) = Tr.priorNetWorth P v n :=
    rawPriorWorthOf_cast Tr P Q n hQ
      (fun i hi => support_subset_supportUpTo Tr (le_of_lt hi)) hagree
  rw [hcurrent, hprior] at hle
  exact hle

/-- On a non-shutoff day the Budgeter cannot lose more than the capital available
at the start of that day, in any world live at that date. -/
lemma BudgeterAt_value_ge_neg_available (L : Assessment) (Tr : Trader) (b : ℕ)
    (hb : 0 < b) (P : History) (Q : ℕ → Sentence → ℚ) (n : ℕ)
    (hQ : ∀ day, day < n → ∀ φ, P day φ = (Q day φ : ℝ))
    (hbreach : priorBudgetBreach L Tr b Q n = false)
    (v : PCWorld) (hv : L.Live n v) :
    -((b : ℝ) + Tr.priorNetWorth P v n) ≤ (BudgeterAt L Tr b Q n).value P v.payout := by
  have hsafeLt := (priorBudgetBreach_eq_false_iff L Tr b P Q n hQ).mp hbreach
  have havail : 0 < (b : ℝ) + Tr.priorNetWorth P v n := by
    cases n with
    | zero => simp only [Trader.priorNetWorth, Finset.range_zero, Finset.sum_empty,
                add_zero]
              exact_mod_cast hb
    | succ m =>
        obtain ⟨v', hv', hagree'⟩ := L.nested m (supportUpTo Tr m) v hv
        have hnet : Tr.netWorth P v' m = Tr.netWorth P v m :=
          netWorth_congr_on_support Tr P m
            (fun i hi => support_subset_supportUpTo Tr hi) hagree'
        have hs := hsafeLt m (by omega) v' hv'
        rw [hnet] at hs
        change 0 < (b : ℝ) + Tr.netWorth P v m
        linarith
  have hαpos := budgetScaleFeature_denote_pos L Tr b P Q n
  have hαcap := budgetScaleFeature_denote_le_lossCap L Tr b P Q n hQ v hv
  have hcap := lossCap_floor
    (available := (b : ℝ) + Tr.priorNetWorth P v n)
    (current := (Tr.strat n).value P v.payout) havail
  rw [BudgeterAt]
  simp only [hbreach, Bool.false_eq_true, if_false, Strategy.scaleBy_value]
  by_cases hx : 0 ≤ (Tr.strat n).value P v.payout
  · have hmul : 0 ≤ (budgetScaleFeature L Tr b Q n).denote P *
        (Tr.strat n).value P v.payout := mul_nonneg hαpos.le hx
    linarith
  · have hx' : (Tr.strat n).value P v.payout ≤ 0 := le_of_not_ge hx
    have hmul : (Tr.strat n).value P v.payout *
        lossCap ((b : ℝ) + Tr.priorNetWorth P v n)
          ((Tr.strat n).value P v.payout) ≤
        (Tr.strat n).value P v.payout *
          (budgetScaleFeature L Tr b Q n).denote P :=
      mul_le_mul_of_nonpos_left hαcap hx'
    calc
      -((b : ℝ) + Tr.priorNetWorth P v n) ≤
          (Tr.strat n).value P v.payout *
            lossCap ((b : ℝ) + Tr.priorNetWorth P v n)
              ((Tr.strat n).value P v.payout) := hcap
      _ ≤ (Tr.strat n).value P v.payout *
          (budgetScaleFeature L Tr b Q n).denote P := hmul
      _ = (budgetScaleFeature L Tr b Q n).denote P *
          (Tr.strat n).value P v.payout := mul_comm _ _

/-- `lem:budgeter` part 2: the realized budgeted trader has the uniform global
floor `-b` in every world live on every date. -/
theorem budgetedTrader_netWorth_floor (L : Assessment) (Tr : Trader) (b : ℕ)
    (hb : 0 < b) (P : History) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) :
    ∀ n (v : PCWorld), L.Live n v →
      -(b : ℝ) ≤ (budgetedTrader L Tr b Q).netWorth P v n := by
  intro n
  induction n with
  | zero =>
      intro v hv
      have hbreach : priorBudgetBreach L Tr b Q 0 = false := by
        simp [priorBudgetBreach]
      have hcur := BudgeterAt_value_ge_neg_available L Tr b hb P Q 0
        (fun day _ φ => hQ day φ) hbreach v hv
      simpa [Trader.netWorth, Trader.priorNetWorth, budgetedTrader] using hcur
  | succ n ih =>
      intro v hv
      cases hbreach : priorBudgetBreach L Tr b Q (n + 1) with
      | true =>
          obtain ⟨v', hv', hagree'⟩ := L.nested n (supportUpTo Tr n) v hv
          have hzero : (BudgeterAt L Tr b Q (n + 1)).value P v.payout = 0 := by
            simp [BudgeterAt, hbreach, Strategy.value]
          have hnetEq : (budgetedTrader L Tr b Q).netWorth P v' n
              = (budgetedTrader L Tr b Q).netWorth P v n :=
            netWorth_congr_on_support (budgetedTrader L Tr b Q) P n
              (fun i hi => subset_trans (BudgeterAt_support_subset L Tr b Q i)
                (support_subset_supportUpTo Tr hi)) hagree'
          rw [Trader.netWorth, Finset.sum_range_succ]
          change -(b : ℝ) ≤
            (budgetedTrader L Tr b Q).netWorth P v n +
              (BudgeterAt L Tr b Q (n + 1)).value P v.payout
          rw [hzero, add_zero, ← hnetEq]
          exact ih v' hv'
      | false =>
          have hsafe := (priorBudgetBreach_eq_false_iff L Tr b P Q (n + 1)
            (fun day _ φ => hQ day φ)).mp hbreach
          have hpriorEq :
              (budgetedTrader L Tr b Q).priorNetWorth P v (n + 1) =
                Tr.priorNetWorth P v (n + 1) := by
            unfold Trader.priorNetWorth
            apply Finset.sum_congr rfl
            intro i hi
            simp only [Finset.mem_range] at hi
            change (BudgeterAt L Tr b Q i).value P v.payout =
              (Tr.strat i).value P v.payout
            apply BudgeterAt_value_eq_of_safe L Tr b hb P Q i
              (fun day _ φ => hQ day φ)
            intro m hmi u hu
            exact hsafe m (lt_of_le_of_lt hmi hi) u hu
          have hcur := BudgeterAt_value_ge_neg_available L Tr b hb P Q (n + 1)
            (fun day _ φ => hQ day φ) hbreach v hv
          rw [Trader.netWorth_eq_prior_add, hpriorEq]
          change -(b : ℝ) ≤ Tr.priorNetWorth P v (n + 1) +
            (BudgeterAt L Tr b Q (n + 1)).value P v.payout
          linarith

/-! ### `lem:budgeter` part 3 -/

/-- `lem:budgeter` part 3: an exploiting trader is preserved by some positive
integer budget.  The selected Budgeter is extensionally the original trader on the
given market, so bounded downside and unbounded upside transfer exactly. -/
theorem exists_budgetedTrader_exploits (L : Assessment) (Tr : Trader) (P : History)
    (Q : ℕ → Sentence → ℚ) (hQ : ∀ day φ, P day φ = (Q day φ : ℝ))
    (hEx : L.Exploits Tr P) :
    ∃ b : ℕ, 0 < b ∧ L.Exploits (budgetedTrader L Tr b Q) P := by
  obtain ⟨a, ha⟩ := hEx.1
  obtain ⟨b₀, hb₀⟩ := exists_nat_gt (-a)
  refine ⟨b₀ + 1, by omega, ?_⟩
  have hba : -((b₀ + 1 : ℕ) : ℝ) < a := by
    have hbcast : ((b₀ + 1 : ℕ) : ℝ) = (b₀ : ℝ) + 1 := by push_cast; ring
    rw [hbcast]; linarith
  have hsafe : ∀ n, ∀ v : PCWorld, L.Live n v →
      -((b₀ + 1 : ℕ) : ℝ) < Tr.netWorth P v n := by
    intro n v hv
    exact hba.trans_le (ha ⟨n, v, hv, rfl⟩)
  have hday : ∀ n (w : Sentence → ℝ),
      (BudgeterAt L Tr (b₀ + 1) Q n).value P w = (Tr.strat n).value P w := by
    intro n w
    exact BudgeterAt_value_eq_of_safe L Tr (b₀ + 1) (by omega) P Q n
      (fun day _ φ => hQ day φ) (fun m _ v hv => hsafe m v hv) w
  have hnet : ∀ n v,
      (budgetedTrader L Tr (b₀ + 1) Q).netWorth P v n = Tr.netWorth P v n := by
    intro n v
    unfold Trader.netWorth
    exact Finset.sum_congr rfl fun i _ => hday i v.payout
  have hassess : L.plausibleAssessments (budgetedTrader L Tr (b₀ + 1) Q) P =
      L.plausibleAssessments Tr P := by
    ext x
    constructor
    · rintro ⟨n, v, hv, rfl⟩; exact ⟨n, v, hv, by rw [hnet]⟩
    · rintro ⟨n, v, hv, rfl⟩; exact ⟨n, v, hv, by rw [hnet]⟩
  unfold Assessment.Exploits
  rw [hassess]
  exact hEx

/-! ## The deductive specialization

At `L = ofDeductiveProcess DP` the generalized Budgeter is the source's Budgeter:
not the same syntax — the two enumerate different finite lists — but the same
function of the market history, hence the same trader.  That equality is what
earns the word "generalization": the source construction is an instance, not an
analogue. -/

private lemma listMin_denote_ge (es : List EF) (P : History) (x : ℝ)
    (hx : x ≤ 1) (h : ∀ e ∈ es, x ≤ e.denote P) : x ≤ (EF.listMin es).denote P := by
  induction es with
  | nil => simpa [EF.listMin] using hx
  | cons e es ih =>
      simp only [EF.listMin, List.foldr_cons, EF.denote_min]
      change x ≤ Min.min (e.denote P) ((EF.listMin es).denote P)
      exact le_min (h e (by simp)) (ih (fun y hy => h y (by simp [hy])))

/-- Each member of the generalized scaling list is the loss cap of a live world. -/
private lemma mem_budgetScaleFeature_list (L : Assessment) (Tr : Trader) (b : ℕ)
    (P : History) (Q : ℕ → Sentence → ℚ) (n : ℕ)
    (hQ : ∀ day, day < n → ∀ φ, P day φ = (Q day φ : ℝ))
    {e : EF} (he : e ∈ (L.tables n (supportUpTo Tr n)).map fun w =>
      budgetWorldScaleOf Tr b Q w n) :
    ∃ v : PCWorld, L.Live n v ∧ e.denote P =
      lossCap ((b : ℝ) + Tr.priorNetWorth P v n)
        ((Tr.strat n).value P v.payout) := by
  simp only [List.mem_map] at he
  obtain ⟨w, hw, rfl⟩ := he
  obtain ⟨v, hv, hagree⟩ := L.tables_sound n (supportUpTo Tr n) w hw
  refine ⟨v, hv, ?_⟩
  rw [budgetWorldScaleOf_denote,
    value_eq_of_payoutAgrees (Tr.strat n) P
      (support_subset_supportUpTo Tr (le_refl n)) hagree,
    rawPriorWorthOf_cast Tr P Q n hQ
      (fun i hi => support_subset_supportUpTo Tr (le_of_lt hi)) hagree]

/-- **Deductive specialization of the scaling factor.** -/
theorem budgetScaleFeature_ofDeductiveProcess_denote (DP : DeductiveProcess)
    (Tr : Trader) (b : ℕ) (P : History) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) (n : ℕ) :
    (budgetScaleFeature (ofDeductiveProcess DP) Tr b Q n).denote P =
      (LogicalInduction.budgetScaleFeature DP Tr b Q n).denote P := by
  apply le_antisymm
  · -- the generalized infimum is below every clause of the source's list
    apply listMin_denote_ge
    · exact budgetScaleFeature_denote_le_one (ofDeductiveProcess DP) Tr b P Q n
    · intro e he
      simp only [List.mem_map, List.mem_filter] at he
      obtain ⟨bits, ⟨_, hcons⟩, rfl⟩ := he
      set u := finiteAtomTable (budgetAtoms DP Tr n) bits with hu
      have hv : (boolPCWorld u).ConsistentWith (DP.D n) :=
        (tableConsistent_eq_true_iff u (DP.D n)).mp hcons
      have hle := budgetScaleFeature_denote_le_lossCap (ofDeductiveProcess DP) Tr b
        P Q n (fun day _ φ => hQ day φ) (boolPCWorld u) hv
      have hprior := rawPriorWorthRat_cast Tr P Q hQ u n
      rw [budgetWorldScale_denote Tr b P Q, ← lossCap]
      rw [Trader.priorNetWorth] at hle
      rw [hprior]
      exact hle
  · -- the source's infimum is below every clause of the generalized list
    apply listMin_denote_ge
    · exact LogicalInduction.budgetScaleFeature_denote_le_one DP Tr b P Q
        (fun day φ => hQ day φ) n
    · intro e he
      obtain ⟨v, hv, hval⟩ := mem_budgetScaleFeature_list (ofDeductiveProcess DP) Tr b
        P Q n (fun day _ φ => hQ day φ) he
      rw [hval]
      exact LogicalInduction.budgetScaleFeature_denote_le_lossCap DP Tr b P Q hQ n v hv

/-- **Deductive specialization of the shutoff test.** -/
theorem priorBudgetBreach_ofDeductiveProcess (DP : DeductiveProcess) (Tr : Trader)
    (b : ℕ) (P : History) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) (n : ℕ) :
    priorBudgetBreach (ofDeductiveProcess DP) Tr b Q n =
      LogicalInduction.priorBudgetBreach DP Tr b Q n := by
  have hiff : priorBudgetBreach (ofDeductiveProcess DP) Tr b Q n = false ↔
      LogicalInduction.priorBudgetBreach DP Tr b Q n = false := by
    rw [priorBudgetBreach_eq_false_iff (ofDeductiveProcess DP) Tr b P Q n
        (fun day _ φ => hQ day φ),
      LogicalInduction.priorBudgetBreach_eq_false_iff DP Tr b P Q hQ n]
    exact Iff.rfl
  cases hg : priorBudgetBreach (ofDeductiveProcess DP) Tr b Q n with
  | false => exact (hiff.mp hg).symm
  | true =>
      cases hs : LogicalInduction.priorBudgetBreach DP Tr b Q n with
      | false => exact absurd (hiff.mpr hs) (by rw [hg]; simp)
      | true => rfl

/-- **Deductive specialization of the Budgeter.**  At `L = PC(D)` the generalized
Budgeter has, at every date, the same value in every world as the source's — so it
is the same trader on that market, and the generalized criterion it is built for is
the original criterion (`exploits_ofDeductiveProcess`). -/
theorem BudgeterAt_ofDeductiveProcess_value (DP : DeductiveProcess) (Tr : Trader)
    (b : ℕ) (P : History) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) (n : ℕ) (w : Sentence → ℝ) :
    (BudgeterAt (ofDeductiveProcess DP) Tr b Q n).value P w =
      (LogicalInduction.BudgeterAt DP Tr b Q n).value P w := by
  unfold BudgeterAt LogicalInduction.BudgeterAt
  rw [priorBudgetBreach_ofDeductiveProcess DP Tr b P Q hQ n]
  cases hs : LogicalInduction.priorBudgetBreach DP Tr b Q n
  · simp only [Bool.false_eq_true, if_false, Strategy.scaleBy_value]
    rw [budgetScaleFeature_ofDeductiveProcess_denote DP Tr b P Q hQ n]
  · simp [Strategy.value]

/-- Net worth form of the specialization. -/
theorem budgetedTrader_ofDeductiveProcess_netWorth (DP : DeductiveProcess)
    (Tr : Trader) (b : ℕ) (P : History) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) (n : ℕ) (v : PCWorld) :
    (budgetedTrader (ofDeductiveProcess DP) Tr b Q).netWorth P v n =
      (LogicalInduction.budgetedTrader DP Tr b Q).netWorth P v n := by
  unfold Trader.netWorth
  exact Finset.sum_congr rfl fun i _ =>
    BudgeterAt_ofDeductiveProcess_value DP Tr b P Q hQ i v.payout

/-! ## Separation: an assessment process need not be a deductive one

The lift is not a change of notation.  The process whose only live world is the
all-true valuation satisfies every hypothesis of `Assessment`, and its live set at
any date is `PC(D n)` for no deductive process `D` at all — because `PC(D n)` is
insensitive to the atoms `D n` does not mention, and this one is not. -/

/-- The valuation making every atom true. -/
def allTrue : PCWorld := fun _ => True

/-- The assessment process whose only live world is `allTrue`. -/
noncomputable def allTrueLive : Assessment where
  Live _ v := ∀ a, v a
  tables _ _ := [ratPayout allTrue]
  tables_sound := by
    intro n S w hw
    simp only [List.mem_singleton] at hw
    exact ⟨allTrue, fun _ => trivial, fun φ _ => by rw [hw]⟩
  tables_complete := by
    intro n S v hv
    refine ⟨ratPayout allTrue, List.mem_singleton_self _, fun φ _ => ?_⟩
    have hveq : v = allTrue := funext fun a => propext ⟨fun _ => trivial, fun _ => hv a⟩
    rw [hveq]
  nested := by
    intro n S v hv
    exact ⟨v, hv, fun _ _ => rfl⟩

@[simp] lemma allTrueLive_live (n : ℕ) (v : PCWorld) :
    allTrueLive.Live n v ↔ ∀ a, v a := Iff.rfl

/-- Propositional consistency with a finite stage depends only on the atoms the
stage mentions. -/
lemma consistentWith_congr_of_atoms {D : Finset Sentence} {v v' : PCWorld}
    (h : ∀ a ∈ D.biUnion Sentence.atoms, (v a ↔ v' a)) :
    v.ConsistentWith D ↔ v'.ConsistentWith D := by
  have key : ∀ φ ∈ D, (v.Holds φ ↔ v'.Holds φ) := by
    intro φ hφ
    have hagree : ∀ a ∈ Sentence.atoms φ, decide (v a) = decide (v' a) := by
      intro a ha
      have := h a (Finset.mem_biUnion.mpr ⟨φ, hφ, ha⟩)
      by_cases hva : v a
      · have hv'a : v' a := this.mp hva
        simp [hva, hv'a]
      · have hv'a : ¬ v' a := fun hc => hva (this.mpr hc)
        simp [hva, hv'a]
    have hb := sentenceBool_congr_of_atoms (u := fun a => decide (v a))
      (v := fun a => decide (v' a)) (φ := φ) hagree
    rw [← sentenceBool_decide_world v φ, ← sentenceBool_decide_world v' φ, hb]
  constructor
  · intro hc φ hφ; exact (key φ hφ).mp (hc φ hφ)
  · intro hc φ hφ; exact (key φ hφ).mpr (hc φ hφ)

/-- **The generalization is proper.**  No deductive process has `allTrueLive`'s
live set at any date. -/
theorem allTrueLive_not_deductive (DP : DeductiveProcess) (n : ℕ) :
    ¬ (∀ v : PCWorld, allTrueLive.Live n v ↔ v.ConsistentWith (DP.D n)) := by
  intro h
  have hATc : allTrue.ConsistentWith (DP.D n) :=
    (h allTrue).mp (fun _ => trivial)
  have ha₀ : (((DP.D n).biUnion Sentence.atoms).sup id + 1) ∉
      (DP.D n).biUnion Sentence.atoms := by
    intro hmem
    have hle := Finset.le_sup (f := id) hmem
    simp only [id_eq] at hle
    omega
  set a₀ := (((DP.D n).biUnion Sentence.atoms).sup id + 1) with ha₀def
  set vfresh : PCWorld := fun a => a ≠ a₀ with hvfresh
  have hvc : PCWorld.ConsistentWith vfresh (DP.D n) := by
    refine (consistentWith_congr_of_atoms (D := DP.D n)
      (v := allTrue) (v' := vfresh) ?_).mp hATc
    intro a ha
    have hne : a ≠ a₀ := fun hEq => ha₀ (hEq ▸ ha)
    exact ⟨fun _ => hne, fun _ => trivial⟩
  have hlive := (h vfresh).mpr hvc
  exact hlive a₀ rfl

/-! ## Inhabitation

`Assessment` is not an empty interface, and neither is the deductive instance. -/

/-- The deductive process revealing nothing: every world stays live forever. -/
def emptyProcess : DeductiveProcess where
  D _ := ∅
  mono _ := Finset.Subset.refl _

theorem assessment_is_nonvacuous :
    ∃ L : Assessment, (∀ n v, L.Live n v) ∧ ∀ n S, L.tables n S ≠ [] := by
  refine ⟨ofDeductiveProcess emptyProcess, ?_, ?_⟩
  · intro n v φ hφ; exact absurd hφ (by simp [emptyProcess])
  · intro n S hnil
    obtain ⟨w, hw, _⟩ := (ofDeductiveProcess emptyProcess).tables_complete n S
      allTrue (fun φ hφ => absurd hφ (by simp [emptyProcess]))
    rw [hnil] at hw
    exact absurd hw (by simp)

/-! ## Support-local nesting against global nesting

The construction consumes only the support-local shadow of `L_{t+1} ⊆ L_t`.  That is
strictly weaker, and exactly one condition closes the gap: being determined by finite
restrictions, which is what `PC(D_n)` is and what the limit-semantics properties of
the source's §4 need. -/

/-- Payouts see a sentence only through the atoms it mentions. -/
lemma ratPayout_congr_of_atoms {v v' : PCWorld} {φ : Sentence}
    (h : ∀ a ∈ Sentence.atoms φ, (v a ↔ v' a)) : ratPayout v φ = ratPayout v' φ := by
  have hagree : ∀ a ∈ Sentence.atoms φ, decide (v a) = decide (v' a) := by
    intro a ha
    have hiff := h a ha
    by_cases hva : v a
    · have : v' a := hiff.mp hva
      simp [hva, this]
    · have : ¬ v' a := fun hc => hva (hiff.mpr hc)
      simp [hva, this]
  have hb := sentenceBool_congr_of_atoms (u := fun a => decide (v a))
    (v := fun a => decide (v' a)) (φ := φ) hagree
  have hv : v.Holds φ ↔ v'.Holds φ := by
    rw [← sentenceBool_decide_world v φ, ← sentenceBool_decide_world v' φ, hb]
  unfold ratPayout
  by_cases hh : v.Holds φ
  · simp [hh, hv.mp hh]
  · have : ¬ v'.Holds φ := fun hc => hh (hv.mpr hc)
    simp [hh, this]

/-- A world set is **finitely determined** when membership is forced by having every
finite restriction realised inside it.  `PC(D)` is: its membership condition reads
finitely many sentences. -/
def FiniteDetermined (S : PCWorld → Prop) : Prop :=
  ∀ v : PCWorld,
    (∀ A : Finset Sentence, ∃ u, S u ∧ ∀ φ ∈ A, ratPayout u φ = ratPayout v φ) → S v

lemma finiteDetermined_consistentWith (D : Finset Sentence) :
    FiniteDetermined (fun v => v.ConsistentWith D) := by
  intro v h
  obtain ⟨u, hu, hagree⟩ := h D
  intro φ hφ
  have hpay := hagree φ hφ
  have : ratPayout u φ = 1 := by unfold ratPayout; simp [hu φ hφ]
  rw [this] at hpay
  unfold ratPayout at hpay
  by_contra hv
  simp [hv] at hpay

/-- **Closedness closes the gap.**  For a finitely-determined family, support-local
nesting gives global nesting. -/
theorem Assessment.live_subset_of_finiteDetermined (L : Assessment) (n : ℕ)
    (hdet : FiniteDetermined (L.Live n)) {v : PCWorld} (hv : L.Live (n + 1) v) :
    L.Live n v := by
  apply hdet v
  intro A
  obtain ⟨u, hu, hagree⟩ := L.nested n A v hv
  exact ⟨u, hu, hagree⟩

/-- A fresh atom for a finite set of sentences. -/
private def freshAtom (A : Finset Sentence) : ℕ :=
  (A.biUnion Sentence.atoms).sup id + 1

private lemma freshAtom_not_mem (A : Finset Sentence) {φ : Sentence} (hφ : φ ∈ A) :
    freshAtom A ∉ Sentence.atoms φ := by
  intro hmem
  have hle := Finset.le_sup (f := id)
    (Finset.mem_biUnion.mpr ⟨φ, hφ, hmem⟩)
  simp only [id_eq, freshAtom] at hle
  omega

/-- Falsifying a fresh atom does not change any payout on the given finite set. -/
private lemma ratPayout_flipFresh (A : Finset Sentence) (v : PCWorld) {φ : Sentence}
    (hφ : φ ∈ A) :
    ratPayout (fun a => v a ∧ a ≠ freshAtom A) φ = ratPayout v φ := by
  apply ratPayout_congr_of_atoms
  intro a ha
  have hne : a ≠ freshAtom A := fun hEq => freshAtom_not_mem A hφ (hEq ▸ ha)
  exact ⟨fun h => h.1, fun h => ⟨h, hne⟩⟩

/-- The assessment process that is *everything but the all-true world* at date `0` and
`{allTrue}` from date `1` on. -/
noncomputable def lateAllTrueLive : Assessment where
  Live n v := match n with
    | 0 => ∃ a, ¬ v a
    | _ + 1 => ∀ a, v a
  tables n S := match n with
    | 0 => deductiveRestrict emptyProcess 0 S
    | _ + 1 => [ratPayout allTrue]
  tables_sound := by
    intro n S w hw
    match n with
    | 0 =>
        obtain ⟨u, _, hagree⟩ := deductiveRestrict_sound emptyProcess 0 S w hw
        refine ⟨fun a => u a ∧ a ≠ freshAtom S, ⟨freshAtom S, by simp⟩, ?_⟩
        intro φ hφ
        rw [hagree φ hφ, ← ratPayout_flipFresh S u hφ]
    | _ + 1 =>
        simp only [List.mem_singleton] at hw
        exact ⟨allTrue, fun _ => trivial, fun φ _ => by rw [hw]⟩
  tables_complete := by
    intro n S v hv
    match n with
    | 0 =>
        exact deductiveRestrict_complete emptyProcess 0 S v
          (fun φ hφ => absurd hφ (by simp [emptyProcess]))
    | _ + 1 =>
        refine ⟨ratPayout allTrue, List.mem_singleton_self _, fun φ _ => ?_⟩
        have hveq : v = allTrue :=
          funext fun a => propext ⟨fun _ => trivial, fun _ => hv a⟩
        rw [hveq]
  nested := by
    intro n S v hv
    match n with
    | 0 =>
        refine ⟨fun a => v a ∧ a ≠ freshAtom S, ⟨freshAtom S, by simp⟩, ?_⟩
        intro φ hφ
        exact ratPayout_flipFresh S v hφ
    | _ + 1 =>
        exact ⟨v, hv, fun _ _ => rfl⟩

/-- **Support-local nesting is strictly weaker than global nesting.**  `lateAllTrueLive`
satisfies the interface — so the whole lift applies to it — while `Live 1 ⊆ Live 0`
fails. -/
theorem lateAllTrueLive_not_globally_nested :
    ¬ (∀ (v : PCWorld), lateAllTrueLive.Live 1 v → lateAllTrueLive.Live 0 v) := by
  intro h
  obtain ⟨a, ha⟩ := h allTrue (fun _ => trivial)
  exact ha trivial

/-- And it is not finitely determined at date `0`, which is consistent with
`live_subset_of_finiteDetermined`. -/
theorem lateAllTrueLive_not_finiteDetermined :
    ¬ FiniteDetermined (lateAllTrueLive.Live 0) := by
  intro hdet
  have := lateAllTrueLive.live_subset_of_finiteDetermined 0 hdet
    (v := allTrue) (fun _ => trivial)
  obtain ⟨a, ha⟩ := this
  exact ha trivial

end Workspace.Normativity.Contrib.AssessmentProcess

#print axioms Workspace.Normativity.Contrib.AssessmentProcess.payout_eq_ratPayout
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.Assessment.nested_le
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.ofDeductiveProcess
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.exploits_ofDeductiveProcess
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.netWorth_congr_on_support
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.worldValueFeatureOf_denote
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.rawWorthOf_cast
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.BudgeterAt_support_subset
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.BudgeterAt_eq_of_eq_prefix
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.priorBudgetBreach_eq_true_iff
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.priorBudgetBreach_eq_false_iff
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.budgetScaleFeature_denote_eq_one_of_safe
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.BudgeterAt_value_eq_of_safe
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.budgetScaleFeature_denote_le_lossCap
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.BudgeterAt_value_ge_neg_available
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.budgetedTrader_netWorth_floor
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.exists_budgetedTrader_exploits
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.budgetScaleFeature_ofDeductiveProcess_denote
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.priorBudgetBreach_ofDeductiveProcess
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.BudgeterAt_ofDeductiveProcess_value
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.budgetedTrader_ofDeductiveProcess_netWorth
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.consistentWith_congr_of_atoms
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.allTrueLive
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.allTrueLive_not_deductive
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.assessment_is_nonvacuous
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.ratPayout_congr_of_atoms
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.finiteDetermined_consistentWith
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.Assessment.live_subset_of_finiteDetermined
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.lateAllTrueLive
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.lateAllTrueLive_not_globally_nested
#print axioms Workspace.Normativity.Contrib.AssessmentProcess.lateAllTrueLive_not_finiteDetermined
