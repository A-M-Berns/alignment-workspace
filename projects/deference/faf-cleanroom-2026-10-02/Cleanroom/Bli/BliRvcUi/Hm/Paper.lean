import Cleanroom.Bli.BliRvcUi.Hm.Defs
import Cleanroom.Bli.BliRvcUi.Rvc.Defs
import Cleanroom.Bli.BliRvcUi.Limit

/-!
# `bli-rvc-ui` · Hm/Paper: hypothetical marginalization is a theorem over `paperDP T` (T4.2–T4.6)

**The claim (U-L2).** Over FAF's single paper-facing market `paperDP T` (`T` a `Δ₁`,
`𝗥₀`-extending arithmetic theory), the HM literal `⌜F(q)⌝` of a computable table predicate `F`:

* **T4.2** holds in a completed-theory world iff `F q` (`hm_reflected`, FAF's
  `BooleanQuoteCode.reflected` at `paperQuotationPresentation T`) — D-HM in the semantic form.
* **T4.3** enters (or its negation enters) some stage `k`, and from that day on **every** valuation
  coherent relative to the day's stage on an atom set containing the literal's atom prices it
  `[F q]` exactly (`hm_exact_of_coherentOn`): exact HM is an instance of D-PC relative to the
  process **from the entry day** — before day `k` nothing forces the value.
* **T4.4** has limiting belief `[F q]` under every inductor over `paperDP T`; the all-true and
  all-false subsequences of an e.c. code family are priced `→ 1` / `→ 0` (`lic_provind`), and the
  identity code family carries its own e.c. certificate (`sentence_poly`).
* **T4.5** the LUV form: every completed world values `[M](z)` at `M z`, and its grid expectation
  at precision `k` is within `1/k` of `M z` in every completed world — Abram's "known to within ε"
  (thread l. 1165) with ε = the mesh, not a modelling slack.
* **T4.6** N+: the two-entry table `[(5, 2), (7, 0)]`, predicate "sentence code `5` has index
  `≥ 1`": true at the actual code, false at the flipped code `[(5, 0), (7, 2)]`, both evaluated.

**No market anywhere in the definitions** (`Hm/Defs.lean`); `liaHistory (paperDP T)` appears only
as the process's inductor in T4.4.

**Hypothesis (c) of SIST.** `udt-bli-sist` consumes T4.2/T4.3 as the discharge of "hypotheticals
marginalize correctly" over `paperDP T`: an (a)-grade theorem, not an assumption.
-/

namespace Cleanroom.Bli.BliRvcUi

open LogicalInduction LO.Propositional Finset Filter Topology Cleanroom.Bli.BliFound

section Paper

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]

/-- **T4.2 — HM literals are reflected** in every completed-theory world of `paperDP T`
(load-bearing): `v ⊨ ⌜F(q)⌝ ↔ F q`. This is D-HM in the semantic form ("a coherent `ℙ` w.r.t. the
process assigns it `0/1`").
Source: [[bli-program-desiderata]] D-HM, U-L2; talk 2024-10 p. 28; bli-soto-a-014; bli-soto-b-040
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem hm_reflected {F : ℕ → Prop} (hF : ComputablePred F) (q : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) : v.Holds (hmSentence T hF q) ↔ F q :=
  (hmQuote T hF).reflected (paperQuotationPresentation T) q v hv

/-- A true HM literal enters some stage of `paperDP T`.
Source: FAF `quote_positive_enters` at `paperQuotationPresentation T`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem hmSentence_enters {F : ℕ → Prop} (hF : ComputablePred F) {q : ℕ} (hq : F q) :
    ∃ k, hmSentence T hF q ∈ (paperDP T).D k :=
  (paperQuotationPresentation T).quote_positive_enters _ q ((hmQuote T hF).pos_complete q hq)

/-- The negation of a false HM literal enters some stage of `paperDP T`.
Source: FAF `quote_negative_refutes` at `paperQuotationPresentation T`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem hmSentence_neg_enters {F : ℕ → Prop} (hF : ComputablePred F) {q : ℕ} (hq : ¬ F q) :
    ∃ k, ∼hmSentence T hF q ∈ (paperDP T).D k :=
  (paperQuotationPresentation T).quote_negative_refutes _ q ((hmQuote T hF).neg_complete q hq)

/-- A stage-coherent valuation prices a sentence of the stage `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma coherentOn_eq_one_of_mem {D : Finset Sentence} {A : Finset ℕ} {V : Sentence → ℝ}
    (h : CoherentOn D A V) {φ : Sentence} (hφ : φ ∈ D) (hA : sentenceAtomCodes φ ⊆ A) :
    V φ = 1 := by
  obtain ⟨k, W, w, hW, hw0, hw1, hV⟩ := h
  rw [hV φ hA, ← hw1]
  apply Finset.sum_congr rfl
  intro i _
  rw [payout_of_holds (hW i φ hφ), mul_one]

/-- A stage-coherent valuation prices a sentence whose negation is in the stage `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma coherentOn_eq_zero_of_neg_mem {D : Finset Sentence} {A : Finset ℕ} {V : Sentence → ℝ}
    (h : CoherentOn D A V) {φ : Sentence} (hφ : ∼φ ∈ D) (hA : sentenceAtomCodes φ ⊆ A) :
    V φ = 0 := by
  obtain ⟨k, W, w, hW, hw0, hw1, hV⟩ := h
  rw [hV φ hA]
  apply Finset.sum_eq_zero
  intro i _
  rw [payout_of_not_holds ((PCWorld.holds_neg _ _).mp (hW i _ hφ)), mul_zero]

open Classical in
/-- **T4.3 — exact HM is an instance of D-PC relative to the process, from the entry day**
(load-bearing): for every code `q` there is a day `k` such that on every day `n ≥ k`, every
valuation coherent relative to `(paperDP T).D n` on an atom set containing the literal's atom
prices `⌜F(q)⌝` at exactly `[F q]`. The entry day is explicit: before it nothing forces the value.
Source: [[bli-program-desiderata]] U-L2 ("a coherent `ℙ_n` w.r.t. the process assigns it 0/1"),
D-HM; mandate T4.3
Kind: C
Fidelity: exact (finite-day form, entry day explicit)
Hyps: (a) -/
theorem hm_exact_of_coherentOn {F : ℕ → Prop} (hF : ComputablePred F) (q : ℕ) :
    ∃ k, ∀ n ≥ k, ∀ (A : Finset ℕ) (V : Sentence → ℝ), CoherentOn ((paperDP T).D n) A V →
      sentenceAtomCodes (hmSentence T hF q) ⊆ A →
      V (hmSentence T hF q) = if F q then 1 else 0 := by
  by_cases hq : F q
  · obtain ⟨k, hk⟩ := hmSentence_enters T hF hq
    refine ⟨k, fun n hn A V hV hA => ?_⟩
    rw [if_pos hq]
    exact coherentOn_eq_one_of_mem hV ((paperDP T).mono_le hn hk) hA
  · obtain ⟨k, hk⟩ := hmSentence_neg_enters T hF hq
    refine ⟨k, fun n hn A V hV hA => ?_⟩
    rw [if_neg hq]
    exact coherentOn_eq_zero_of_neg_mem hV ((paperDP T).mono_le hn hk) hA

/-- **T4.3 on a finite set of codes**: `HMExact` from some day on, relative to the process.
Source: mandate T4.3; [[bli-program-desiderata]] D-HM
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem hmExact_of_coherentOn {F : ℕ → Prop} (hF : ComputablePred F) (Q : Finset ℕ) :
    ∃ k, ∀ n ≥ k, ∀ (A : Finset ℕ) (V : Sentence → ℝ), CoherentOn ((paperDP T).D n) A V →
      (∀ q ∈ Q, sentenceAtomCodes (hmSentence T hF q) ⊆ A) → HMExact T V hF Q := by
  choose kq hkq using fun q => hm_exact_of_coherentOn T hF q
  refine ⟨Q.sup kq, fun n hn A V hV hA q hq => ?_⟩
  exact hkq q n (le_trans (Finset.le_sup hq) hn) A V hV (hA q hq)

omit [T.Δ₁] in
/-- The identity code family of HM literals is machine-metered (FAF's `sentence_poly`).
Source: FAF `BooleanQuoteCode.sentence_poly`
Kind: L
Fidelity: n/a -/
lemma hmSentence_machineCodes {F : ℕ → Prop} (hF : ComputablePred F) :
    MachineSentenceCodes (hmSentence T hF) :=
  MachineSentenceCodes.ofPolySentenceCodes (hmQuote T hF).sentence_poly

/-! ## T4.5 — the LUV form -/

/-- **T4.5 — every completed-theory world values the HM LUV at the reading**.
Source: FAF `RationalQuoteCode.reflected` at `paperQuotationPresentation T`; mandate T4.5
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem hmLuv_valuesAt {M : ℕ → ℚ} (hM : Computable M) (hMmem : ∀ z, 0 ≤ M z ∧ M z ≤ 1) (z : ℕ)
    (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt (hmLuv T hM hMmem z) (M z : ℝ) :=
  (hmRatQuote T hM hMmem).reflected (paperQuotationPresentation T) z v hv

/-- **T4.5 — "known to within ε", ε = the mesh**: in every completed-theory world the grid
expectation of the HM LUV at precision `k` is within `1/k` of the reading.
Source: thread l. 1165 (Abram: "`[prop](Q)` known to within ε"); FAF `expectApprox_near`
Kind: C
Fidelity: exact (the ε is the grid `1/k`, not a modelling slack)
Hyps: (a) -/
theorem hmLuv_expect_near {M : ℕ → ℚ} (hM : Computable M) (hMmem : ∀ z, 0 ≤ M z ∧ M z ≤ 1)
    (z : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) {k : ℕ} (hk : 0 < k) :
    |(hmLuv T hM hMmem z).expectApprox v.payout k - (M z : ℝ)| ≤ 1 / k :=
  (hmLuv_valuesAt T hM hMmem z v hv).expectApprox_near hk

variable [𝗣𝗔⁻ ⪯ T] [LO.Entailment.Consistent T]

/-- **T4.3's hypothesis package is inhabited (N−)**: at every day, the payout of a
completed-theory world of `paperDP T` is coherent relative to the stage on the literal's atom set.
A single world is the best available without a market; it also shows the entry-day clause is not
vacuous.
Source: audit r1 (fidelity N3, adversarial (e)); FAF `paperDP_nonvacuous`
Kind: N-
Fidelity: n/a -/
theorem hm_exact_of_coherentOn_inhabited {F : ℕ → Prop} (hF : ComputablePred F) (q n : ℕ) :
    ∃ (A : Finset ℕ) (V : Sentence → ℝ), CoherentOn ((paperDP T).D n) A V ∧
      sentenceAtomCodes (hmSentence T hF q) ⊆ A := by
  obtain ⟨v, hv⟩ := paperDP_nonvacuous T
  exact ⟨_, v.payout, ⟨1, fun _ => v, fun _ => 1, fun _ => hv n, fun _ => zero_le_one, by simp,
    fun φ _ => by simp⟩, Finset.Subset.refl _⟩

open Classical in
/-- **T4.4 — the limiting belief of an HM literal is its truth value**, for every inductor over
`paperDP T`.
Source: mandate T4.4; [[bli-program-desiderata]] D-HM (limit form)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem hm_limit {P : History} [IsLogicalInductor P (paperDP T)] {F : ℕ → Prop}
    (hF : ComputablePred F) (q : ℕ) :
    limitingBelief P (hmSentence T hF q) = if F q then 1 else 0 := by
  by_cases hq : F q
  · rw [if_pos hq]
    exact limitingBelief_eq_one_of_theory (paperDP_hworld T) fun v hv =>
      (hm_reflected T hF q v hv).mpr hq
  · rw [if_neg hq]
    exact limitingBelief_eq_zero_of_theory (paperDP_hworld T) fun v hv h =>
      hq ((hm_reflected T hF q v hv).mp h)

open Classical in
/-- **T4.4, day form**: the prices of an HM literal converge to its truth value.
Source: mandate T4.4
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem hm_tendsto {P : History} [IsLogicalInductor P (paperDP T)] {F : ℕ → Prop}
    (hF : ComputablePred F) (q : ℕ) :
    ConvergesTo (fun n => P n (hmSentence T hF q)) (if F q then 1 else 0) := by
  rw [← hm_limit T (P := P) hF q]
  exact lic_limitingBelief_tendsto P _ (paperDP_hworld T) _

/-- **T4.4, sequence form (true subsequence)**: along an e.c. code family whose predicate holds,
the HM literals are priced `→ 1`.
Source: mandate T4.4 ("split into the true and false subsequences via `lic_provind`")
Kind: C
Fidelity: exact
Hyps: (a) `hec` is the code family's e.c. certificate (discharged for the identity family) -/
theorem hm_seq_true {P : History} [IsLogicalInductor P (paperDP T)] {F : ℕ → Prop}
    (hF : ComputablePred F) (q : ℕ → ℕ) (hec : MachineSentenceCodes fun n => hmSentence T hF (q n))
    (hall : ∀ n, F (q n)) : (fun n => P n (hmSentence T hF (q n))) ≈ₙ fun _ => 1 :=
  lic_provind_true P _ _ hec (fun n v hv => (hm_reflected T hF (q n) v hv).mpr (hall n))
    (paperDP_hworld T)

/-- **T4.4, sequence form (false subsequence)**.
Source: mandate T4.4
Kind: C
Fidelity: exact
Hyps: (a) `hec` as above -/
theorem hm_seq_false {P : History} [IsLogicalInductor P (paperDP T)] {F : ℕ → Prop}
    (hF : ComputablePred F) (q : ℕ → ℕ) (hec : MachineSentenceCodes fun n => hmSentence T hF (q n))
    (hnone : ∀ n, ¬ F (q n)) : (fun n => P n (hmSentence T hF (q n))) ≈ₙ fun _ => 0 :=
  lic_provind_false P _ _ hec
    (fun n v hv => (PCWorld.holds_neg v _).mpr fun h => hnone n ((hm_reflected T hF (q n) v hv).mp h))
    (paperDP_hworld T)

/-- **T4.4 at FAF's own inductor** `liaHistory (paperDP T)`, identity code family, all-true case.
Source: mandate T4.4
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem hm_lia_seq_true {F : ℕ → Prop} (hF : ComputablePred F) (hall : ∀ q, F q) :
    (fun n => liaHistory (paperDP T) n (hmSentence T hF n)) ≈ₙ fun _ => 1 :=
  haveI := paperLIA T
  hm_seq_true T hF id (hmSentence_machineCodes T hF) hall

end Paper

/-! ## T4.6 — a concrete two-entry table -/

/-- The actual table code `[(5, 2), (7, 0)]`.
Source: mandate T4.6
Kind: D
Fidelity: n/a -/
def actualTableCode : ℕ := Encodable.encode [((5 : ℕ), (2 : ℕ)), (7, 0)]

/-- The flipped table code `[(5, 0), (7, 2)]`.
Source: mandate T4.6
Kind: D
Fidelity: n/a -/
def flippedTableCode : ℕ := Encodable.encode [((5 : ℕ), (0 : ℕ)), (7, 2)]

/-- The predicate "sentence code `5` has grid index `≥ 1`" holds of the actual table.
Source: mandate T4.6
Kind: L
Fidelity: n/a -/
theorem entryAtLeast_actual : entryAtLeast 5 1 actualTableCode := by
  unfold entryAtLeast actualTableCode
  rw [tableOfCode_encode]
  exact ⟨(5, 2), by simp, rfl, by norm_num⟩

/-- … and fails of the flipped table.
Source: mandate T4.6
Kind: L
Fidelity: n/a -/
theorem not_entryAtLeast_flipped : ¬ entryAtLeast 5 1 flippedTableCode := by
  unfold entryAtLeast flippedTableCode
  rw [tableOfCode_encode]
  rintro ⟨e, he, h5, h1⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact absurd h1 (by norm_num)
  · exact absurd h5 (by norm_num)

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]

/-- **T4.6 (N+)**: both `hm_reflected` instances evaluated — every completed-theory world of
`paperDP T` holds `⌜F(actual)⌝` and fails `⌜F(flipped)⌝`, for `F` = "code `5` has index `≥ 1`".
Source: mandate T4.6
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem hm_witness (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.Holds (hmSentence T (entryAtLeast_computable 5 1) actualTableCode) ∧
    ¬ v.Holds (hmSentence T (entryAtLeast_computable 5 1) flippedTableCode) :=
  ⟨(hm_reflected T _ _ v hv).mpr entryAtLeast_actual,
    fun h => not_entryAtLeast_flipped ((hm_reflected T _ _ v hv).mp h)⟩

/-- The rational reading of the actual table at code `5`, mesh `4`, is `1/2`.
Source: mandate T4.6 (the LUV form's instance)
Kind: L
Fidelity: n/a -/
theorem tableEntryValue_actual : tableEntryValue 5 4 actualTableCode = 1 / 2 := by
  unfold tableEntryValue
  rw [tableEntry_eq_entryOf]
  unfold actualTableCode
  rw [tableOfCode_encode]
  simp [entryOf]
  norm_num [Rat.mkRat_eq_div]

/-- **T4.6, LUV form (N+)**: every completed-theory world values the HM LUV of the reading at the
actual code at exactly `1/2`.
Source: mandate T4.6
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem hmLuv_witness (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt (hmLuv T (tableEntryValue_computable 5 4) (tableEntryValue_mem 5 4) actualTableCode)
      (1 / 2 : ℝ) := by
  have h := hmLuv_valuesAt T (tableEntryValue_computable 5 4) (tableEntryValue_mem 5 4)
    actualTableCode v hv
  rw [tableEntryValue_actual] at h
  simpa using h

end Cleanroom.Bli.BliRvcUi
