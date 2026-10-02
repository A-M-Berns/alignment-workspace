import Cleanroom.Found.DefLattice.BetClass
import Cleanroom.Found.DefLattice.TwoOptionLUV
import LogicalInduction.Framework.Machine.Witnesses

/-!
# def-lattice — audit round 2, adversarial lens: degenerate-model probes

Not imported by the library. Elaborated with `scripts/lean-check`. Each probe is a claim
about the definitions of `Cleanroom.Found.DefLattice` after repair round 1, checked in a
degenerate model (the all-ones expert of round 1's `Vacuity.lean`, the `⊤`/`⊥` literal
indicators, the atom source).

1. `not_value_allOnes` — `Value` is falsifiable: the all-ones expert (quotes tie, least index
   wins) with the menu `{⊥-indicator, ⊤-indicator}` and the follower `⊥-indicator` fails
   `Value` against any history pricing `⊤` at `1` and `⊥` at `0`, for **every** deductive
   process (no consistent world is needed, so an inconsistent theory cannot fake `Value`
   either).
2. `generated_eq_univ_of_not_ec` — junk value of `BetClass.generated`: a base with one
   non-e.d. member generates the universal class (no deference class contains such a base).
3. `hardData`, `hardWeightQuote`, `allOnes_hsur` — the full hypothesis package of
   `value_twoOption_hardAbove` **and** of the `(c)`-graded
   `value_twoOption_hardAbove_of_weightQuote` (including `hsur`) *is* inhabited, by the
   all-ones expert at `s = 1` with `C = W = ⊤-indicator`, `S = XW = X` the atom source; and
   `degenerate_conclusion_iff_hval` — on that inhabitant the theorems' conclusion is the
   hypothesis `hval` restated (`W = C`, `XW = X`, `s = 1`). So the cheapest inhabitant is a
   tautology instance: grade N−, which is why the ledger's "witness partial" is the honest
   status and a constant-expert witness must not be shipped as N+.
4. `value_twoOption_hardAbove_converse` — the converse of the T6d above face is free from
   the same two lemmas (`expect_followed_asympEq`, `expect_const_asympEq`): the source's
   *iff* is available at the LUV level; the package ships one direction.
5. `hardBandQuote`, `not_hardValueReflection_allOnes`, `not_hardTotalTrustAbove_allOnes` —
   the "refuted objects" are refutable in their shipped universal form whenever a sharp
   quote exists: for the all-ones expert the sharp band/cut weight at `s = 1` is the
   `⊤`-indicator, and both predicates fail on a history pricing `⊤` at `1`, `⊥` at `0`.
   (Round 1's N8 caveat — vacuity when no sharp quote exists — is confirmed to be about the
   *expert*, not about the definition.)
-/

namespace Cleanroom.Found.DefLattice.AuditR2

open LogicalInduction Filter Topology

noncomputable section

/-! ## The all-ones expert and the two literal constants -/

/-- The expert pricing every sentence at `1`, with the successor deferral (round 1). -/
def allOnes (DP : DeductiveProcess) : Expert DP :=
  ⟨fun _ _ => 1, succDeferral, fun _ _ => ⟨zero_le_one, le_refl 1⟩⟩

/-- Its estimate of every LUV is `1`. -/
lemma allOnes_estimate (DP : DeductiveProcess) (X : ℕ → LUV) (n : ℕ) :
    (allOnes DP).estimate X n = 1 := by
  unfold Expert.estimate LUV.expect LUV.expectApprox
  simp only [allOnes, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hk : ((succDeferral.f n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  exact inv_mul_cancel₀ hk

lemma not_holds_bot (v : PCWorld) : ¬ v.Holds (⊥ : Sentence) := by
  simp [PCWorld.Holds, LO.Propositional.Formula.Boolean.val]

/-- `literalIndicator ⊤` is valued `1` in every world (round 1). -/
lemma literalIndicator_top_valuesAt (v : PCWorld) : v.ValuesAt (literalIndicator ⊤) 1 := by
  refine ⟨zero_le_one, le_refl 1, fun r => ⟨fun hr => ?_, fun hr => ?_⟩⟩
  · have hr1 : r < 1 := by exact_mod_cast hr
    unfold literalIndicator
    dsimp only
    split_ifs <;> exact PCWorld.holds_top v
  · have hr1 : ¬ r < 1 := by
      have : (1 : ℝ) < r := hr
      exact not_lt.mpr (by exact_mod_cast this.le)
    have hr0 : ¬ r < 0 := fun hc => hr1 (hc.trans zero_lt_one)
    simp only [literalIndicator, if_neg hr0, if_neg hr1]
    exact not_holds_bot v

/-- `literalIndicator ⊥` is valued `0` in every world. -/
lemma literalIndicator_bot_valuesAt (v : PCWorld) : v.ValuesAt (literalIndicator ⊥) 0 := by
  refine ⟨le_refl 0, zero_le_one, fun r => ⟨fun hr => ?_, fun hr => ?_⟩⟩
  · have hr0 : r < 0 := by exact_mod_cast hr
    simp only [literalIndicator, if_pos hr0]
    exact PCWorld.holds_top v
  · have hr0 : ¬ r < 0 := by
      have : (0 : ℝ) < r := hr
      exact not_lt.mpr (by exact_mod_cast this.le)
    simp only [literalIndicator, if_neg hr0]
    split_ifs <;> exact not_holds_bot v

/-- The constant `⊤`-indicator family (valued `1`). -/
abbrev topFam : ℕ → LUV := fun _ => literalIndicator ⊤

/-- The constant `⊥`-indicator family (valued `0`). -/
abbrev botFam : ℕ → LUV := fun _ => literalIndicator ⊥

lemma topFam_codes : LUV.MachineThresholdCodeSeq topFam :=
  literalIndicator_machineThresholdCodeSeq (MachineSentenceCodes.const (⊤ : Sentence))

lemma botFam_codes : LUV.MachineThresholdCodeSeq botFam :=
  literalIndicator_machineThresholdCodeSeq (MachineSentenceCodes.const (⊥ : Sentence))

/-- The day-varying atom source `n ↦ literalIndicator ⌜aₙ⌝` (the package's witness source). -/
abbrev atomSource : ℕ → LUV := fun n => literalIndicator (LO.Propositional.Formula.atom n)

lemma atomSource_codes : LUV.MachineThresholdCodeSeq atomSource :=
  literalIndicator_machineThresholdCodeSeq machineSentenceCodes_atom

/-! ## Probe 1: `Value` is falsifiable (for every deductive process) -/

/-- The menu `{⊥-indicator, ⊤-indicator}`. -/
def botTopMenu : Menu 1 := twoOptionMenu botFam topFam botFam_codes topFam_codes

lemma botTopMenu_valued (DP : DeductiveProcess) : botTopMenu.Valued DP := by
  intro j n v hv
  by_cases h : j = 0
  · subst h
    show ∃ x, v.ValuesAt ((twoOptionMenu botFam topFam botFam_codes topFam_codes).O 0 n) x
    rw [twoOptionMenu_O_zero]
    exact ⟨_, literalIndicator_valuesAt ⊥ DP hv⟩
  · have h1 : j = 1 := by
      revert h
      generalize j = a
      intro h
      fin_cases a
      · exact absurd rfl h
      · rfl
    subst h1
    show ∃ x, v.ValuesAt ((twoOptionMenu botFam topFam botFam_codes topFam_codes).O 1 n) x
    rw [twoOptionMenu_O_one]
    exact ⟨_, literalIndicator_valuesAt ⊤ DP hv⟩

/-- Quotes tie at `1`, so the least index `0` (the `⊥`-indicator) is selected every day. -/
lemma botTopMenu_argmax (DP : DeductiveProcess) (n : ℕ) :
    botTopMenu.argmax (allOnes DP) n = 0 := by
  rw [Menu.argmax_two]
  simp [Menu.quote, allOnes_estimate]

/-- The `⊥`-indicator follows the all-ones expert on that menu (no consistency needed). -/
lemma botFam_follows (DP : DeductiveProcess) :
    Follows DP (allOnes DP) botTopMenu botFam := by
  intro n v _ x hx
  rw [botTopMenu_argmax] at hx
  have hO : botTopMenu.O 0 = botFam := twoOptionMenu_O_zero _ _ _ _
  rw [hO] at hx
  exact hx

/-- **`Value` fails for the all-ones expert** against any history pricing `⊤` at `1` and `⊥`
at `0`, for every `DP`: the follower has expectation `0`, the fixed option `⊤` has `1`. -/
theorem not_value_allOnes (DP : DeductiveProcess) (P : History)
    (hTop : ∀ n, P n ⊤ = 1) (hBot : ∀ n, P n ⊥ = 0) : ¬ Value P DP (allOnes DP) := by
  intro h
  have h1 := h 1 botTopMenu (botTopMenu_valued DP) botFam botFam_codes (botFam_follows DP) 1
  have hO : botTopMenu.O 1 = topFam := twoOptionMenu_O_one _ _ _ _
  rw [hO] at h1
  unfold AsympGE AsympLE at h1
  obtain ⟨n, hn⟩ := (h1 (1 / 2) (by norm_num)).exists
  simp only [botFam, topFam, literalIndicator_expect, hTop, hBot] at hn
  norm_num at hn

/-! ## Probe 2: `generated` of a non-e.d. base is the universal class -/

theorem generated_eq_univ_of_not_ec {DP : DeductiveProcess} {E : Expert DP}
    (base : Set (ℕ → LUV)) (X₀ : ℕ → LUV) (h₀ : X₀ ∈ base)
    (hne : ¬ LUV.MachineThresholdCodeSeq X₀) :
    (BetClass.generated DP E base).carrier = (BetClass.univ DP E).carrier := by
  ext X
  constructor
  · intro hX
    exact hX.1
  · intro hX
    exact ⟨hX, fun C _ hb => absurd (C.codes X₀ (hb h₀)) hne⟩

/-! ## Probe 3: the T6d hypothesis packages are inhabited, degenerately -/

/-- `HardTwoOptionData` for the all-ones expert at `s = 1`: `C = W = ⊤`-indicator,
`S = XW = X` the atom source. Every clause holds because every estimate is `1`. -/
def hardData (DP : DeductiveProcess) :
    HardTwoOptionData DP (allOnes DP) atomSource topFam atomSource topFam atomSource 1 where
  codes_X := atomSource_codes
  codes_C := topFam_codes
  codes_S := atomSource_codes
  codes_W := topFam_codes
  codes_XW := atomSource_codes
  valued_X := fun n v hv => ⟨_, literalIndicator_valuesAt _ DP hv⟩
  const_reflected := fun _ v _ => by simpa using literalIndicator_top_valuesAt v
  weight_reflected := fun _ v _ => by
    simp only [allOnes_estimate, le_refl, ite_true]
    exact literalIndicator_top_valuesAt v
  product_reflected := fun _ v _ x hx => by
    simpa [allOnes_estimate] using hx
  follows := by
    intro n v _ x hx
    have hargmax :
        (twoOptionMenu atomSource topFam atomSource_codes topFam_codes).argmax (allOnes DP) n
          = 0 := by
      rw [Menu.argmax_two]
      simp [Menu.quote, allOnes_estimate]
    rw [hargmax, twoOptionMenu_O_zero] at hx
    exact hx

/-- The hard `WeightQuote` at `hardAbove 1` with `slack ≡ 0`, for the same data. -/
def hardWeightQuote (DP : DeductiveProcess) :
    WeightQuote DP (allOnes DP) atomSource (hardAbove 1) topFam atomSource where
  weight_codes := topFam_codes
  product_codes := atomSource_codes
  slack := fun _ => 0
  slack_tendsto := tendsto_const_nhds
  source_valued := fun n v hv => ⟨_, literalIndicator_valuesAt _ DP hv⟩
  weight_reflected := fun _ v _ => by
    simp only [hardAbove, allOnes_estimate, Rat.cast_one, le_refl, ite_true]
    exact literalIndicator_top_valuesAt v
  product_reflected := fun _ v _ x hx =>
    ⟨x, by simpa using hx, by simp [hardAbove, allOnes_estimate]⟩

/-- The surrogate coherence `hsur` of the `(c)` corollary holds for the all-ones expert. -/
lemma allOnes_hsur (DP : DeductiveProcess) (n : ℕ) :
    (allOnes DP).estimate topFam n = ((1 : ℚ) : ℝ) := by
  simpa using allOnes_estimate DP topFam n

/-- On the degenerate inhabitant the T6d conclusion *is* the hypothesis `hval`: with `W = C`
and `XW = X` at `s = 1`, `E(XW) − s·E(W) ≳ₙ 0` is `E(X) ≳ₙ E(C)` verbatim. -/
theorem degenerate_conclusion_iff_hval (P : History) :
    ((fun n => (atomSource n).expect P n - ((1 : ℚ) : ℝ) * (topFam n).expect P n) ≳ₙ
        (fun _ => (0 : ℝ))) ↔
      (fun n => (atomSource n).expect P n) ≳ₙ (fun n => (topFam n).expect P n) := by
  rw [soft_above_iff_unnormalized]
  simp only [Rat.cast_one, one_mul]

/-! ## Probe 4: the converse of the T6d above face is free -/

theorem value_twoOption_hardAbove_converse (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] {E : Expert DP}
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {X C S W XW : ℕ → LUV} {s : ℚ} (d : HardTwoOptionData DP E X C S W XW s)
    (hcut : (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≳ₙ
      (fun _ => (0 : ℝ))) :
    (fun n => (S n).expect P n) ≳ₙ (fun n => (C n).expect P n) := by
  have hlin := d.expect_followed_asympEq P hworld
  have hconst := d.expect_const_asympEq P hworld
  have h1 : (fun _ => (s : ℝ)) ≲ₙ
      (fun n => (XW n).expect P n + (s : ℝ) - (s : ℝ) * (W n).expect P n) := by
    unfold AsympGE AsympLE at hcut
    unfold AsympLE
    intro ε hε
    filter_upwards [hcut ε hε] with n hn
    linarith
  have h2 : (fun _ => (s : ℝ)) ≲ₙ (fun n => (S n).expect P n) :=
    AsympLE.trans_asympEq h1 hlin.symm
  exact AsympEq.trans_asympLE hconst h2

/-! ## Probe 5: the refuted objects are refutable when a sharp quote exists -/

/-- A sharp-band `WeightQuote` at `hardBand 1` for the all-ones expert: the band weight at
estimate `1` is `1`, so the `⊤`-indicator reflects it and the product is the source. -/
def hardBandQuote (DP : DeductiveProcess) :
    WeightQuote DP (allOnes DP) botFam (hardBand 1) topFam botFam where
  weight_codes := topFam_codes
  product_codes := botFam_codes
  slack := fun _ => 0
  slack_tendsto := tendsto_const_nhds
  source_valued := fun n v hv => ⟨_, literalIndicator_valuesAt _ DP hv⟩
  weight_reflected := fun _ v _ => by
    simp only [hardBand, allOnes_estimate, Rat.cast_one, ite_true]
    exact literalIndicator_top_valuesAt v
  product_reflected := fun _ v _ x hx =>
    ⟨x, by simpa using hx, by simp [hardBand, allOnes_estimate]⟩

/-- A sharp-cut `WeightQuote` at `hardAbove 1`, same data. -/
def hardCutQuote (DP : DeductiveProcess) :
    WeightQuote DP (allOnes DP) botFam (hardAbove 1) topFam botFam where
  weight_codes := topFam_codes
  product_codes := botFam_codes
  slack := fun _ => 0
  slack_tendsto := tendsto_const_nhds
  source_valued := fun n v hv => ⟨_, literalIndicator_valuesAt _ DP hv⟩
  weight_reflected := fun _ v _ => by
    simp only [hardAbove, allOnes_estimate, Rat.cast_one, le_refl, ite_true]
    exact literalIndicator_top_valuesAt v
  product_reflected := fun _ v _ x hx =>
    ⟨x, by simpa using hx, by simp [hardAbove, allOnes_estimate]⟩

/-- **`HardValueReflection` fails for the all-ones expert** on a history pricing `⊤` at `1`
and `⊥` at `0`: at `s = 1` the sharp-band package is inhabited and the above face demands
`E(⊥) − 1·E(⊤) = −1 ≳ₙ 0`. -/
theorem not_hardValueReflection_allOnes (DP : DeductiveProcess) (P : History)
    (hTop : ∀ n, P n ⊤ = 1) (hBot : ∀ n, P n ⊥ = 0) :
    ¬ HardValueReflection P DP (allOnes DP) := by
  intro h
  have h1 := (h 1).1 botFam topFam botFam botFam_codes (hardBandQuote DP)
  unfold AsympGE AsympLE at h1
  obtain ⟨n, hn⟩ := (h1 (1 / 2) (by norm_num)).exists
  simp only [botFam, topFam, literalIndicator_expect, hTop, hBot] at hn
  norm_num at hn

/-- **`HardTotalTrustAbove … 1` fails for the all-ones expert**, same history, same reason. -/
theorem not_hardTotalTrustAbove_allOnes (DP : DeductiveProcess) (P : History)
    (hTop : ∀ n, P n ⊤ = 1) (hBot : ∀ n, P n ⊥ = 0) :
    ¬ HardTotalTrustAbove P DP (allOnes DP) 1 := by
  intro h
  have h1 := h botFam topFam botFam botFam_codes (hardCutQuote DP)
  unfold AsympGE AsympLE at h1
  obtain ⟨n, hn⟩ := (h1 (1 / 2) (by norm_num)).exists
  simp only [botFam, topFam, literalIndicator_expect, hTop, hBot] at hn
  norm_num at hn

end

end Cleanroom.Found.DefLattice.AuditR2
