import Cleanroom.Deference.DefSqueezeDiamond.Reindex

/-!
# `def-argmax-value` · Calc: deferred-day provability-induction corollaries and refutation calculus

Infrastructure shared by the refutations and the lemmas: the shapes of deferred-day
`thm:expprovind` (`def-squeeze-diamond`'s `Reindex` endpoints) that the package consumes —
a LUV valued within slack of a constant times a valued LUV (`expect_deferred_const_mul`), of a
constant (`expect_deferred_const`), the deferred-day coherence of a sentence and its negation
(`deferred_neg_coherence`) — the same-day constant-option expectation
(`expect_constLUV_asympEq`), and the one lemma every refutation ends with: a difference that
converges to a negative number is not `≳ₙ 0` (`not_asympGE_of_tendsto_neg`).

Not construction-facing; no FAF construction imports.
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows
open Cleanroom.Deference.DefSelfTrust Cleanroom.Deference.DefSqueezeDiamond

noncomputable section

/-! ## The ramp at and below its threshold -/

/-- The ramp vanishes at or below its threshold.
Source: none: infrastructure (FAF `ctsInd`)
Kind: L
Fidelity: n/a -/
theorem ctsInd_eq_zero_of_le {δ : ℚ} (hδ : 0 < δ) {x y : ℝ} (h : x ≤ y) : ctsInd δ x y = 0 := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold ctsInd
  have : (x - y) / (δ : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδR.le
  rw [max_eq_left this, min_eq_right zero_le_one]

/-! ## Refutation calculus -/

/-- **A difference converging to a negative limit is not asymptotically nonnegative**: the
negation every refutation of a `≳ₙ` claim reduces to.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem not_asympGE_of_tendsto_neg {a b : ℕ → ℝ} {c : ℝ} (hc : c < 0)
    (h : Tendsto (fun n => a n - b n) atTop (𝓝 c)) : ¬ (a ≳ₙ b) := by
  intro hge
  have hev := hge (-c / 2) (by linarith)
  have hev2 := (tendsto_order.1 h).2 (c / 2) (by linarith)
  obtain ⟨n, hn1, hn2⟩ := (hev.and hev2).exists
  linarith

/-- A sequence `≈ₙ` a constant is a `Tendsto`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tendsto_of_asympEq_const {a : ℕ → ℝ} {c : ℝ} (h : a ≈ₙ (fun _ => c)) :
    Tendsto a atTop (𝓝 c) := by
  unfold AsympEq at h
  have := h.add (tendsto_const_nhds (x := c))
  simpa using this

/-- A `Tendsto` to a constant is `≈ₙ` that constant.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem asympEq_const_of_tendsto {a : ℕ → ℝ} {c : ℝ} (h : Tendsto a atTop (𝓝 c)) :
    a ≈ₙ (fun _ => c) := by
  unfold AsympEq
  have := h.sub (tendsto_const_nhds (x := c))
  simpa using this

/-! ## Same-day: the constant option -/

/-- **The expectation of the constant option converges to its value**: `E_n(const s) → s`
(`thm:expprovind` on the exact bet `const s − s`); `def-lattice-arrows`'
`expect_probeConst_asympEq` for every `s ∈ [0,1]`.
Source: none: infrastructure (FAF `lic_expect_combination_provind_eq`)
Kind: L
Fidelity: n/a -/
theorem expect_constLUV_asympEq {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {s : ℚ} (hs : 0 ≤ s ∧ s ≤ 1) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (constLUV s).expect P n) ≈ₙ (fun _ => (s : ℝ)) := by
  have h := expect_listComb_eq_of_slack (P := P) (DP := DP) (constStream_splice 0)
    (B := 0) (fun _ => by simp) (ts := [(1, fun _ => constLUV s)])
    (fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact constLUV_codes hs.1)
    (listComb_worldValued _ (fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp; exact constLUV_valued hs DP))
    (s : ℝ) (slack := fun _ => 0) tendsto_const_nhds
    (fun n v hv ν hν => by
      have := listComb_valuesAt_mem hν (p := (1, fun _ => constLUV s)) (List.mem_singleton_self _)
      rw [listComb_value]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [this.eq (constLUV_valuesAt hs v)]
      simp) hworld
  refine (tendsto_congr (fun n => ?_)).mp h
  simp [listComb_expect]

/-! ## Deferred-day corollaries -/

section Deferred

variable {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]

/-- **Deferred-day provind, product-with-constant form**: if `Y n` is valued within a vanishing
`slack n` of `c · x` whenever the valued `X n` is valued `x`, then
`(fun n => (Y n).expect P (f n)) ≈ₙ (fun n => c · (X n).expect P (f n))`.
Source: none: infrastructure (`def-squeeze-diamond` `expect_deferred_asympEq_zero_of_slack`)
Kind: L
Fidelity: n/a
Hyps: (a); `hf` -/
theorem expect_deferred_const_mul (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f)
    (c : ℚ) {X Y : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X)
    (hY : LUV.MachineThresholdCodeSeq Y) (hXv : Valued DP X) (slack : ℕ → ℝ)
    (hslack : Tendsto slack atTop (𝓝 0))
    (hr : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∀ x, v.ValuesAt (X n) x →
      ∃ z, v.ValuesAt (Y n) z ∧ |z - (c : ℝ) * x| ≤ slack n)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (Y n).expect P (f n)) ≈ₙ (fun n => (c : ℝ) * (X n).expect P (f n)) := by
  have hYv : Valued DP Y := fun n v hv => by
    obtain ⟨x, hx⟩ := hXv n v hv
    obtain ⟨z, hz, -⟩ := hr n v hv x hx
    exact ⟨z, hz⟩
  set terms : List ((ℕ → EF) × (ℕ → LUV)) :=
    [(fun _ => EF.const 1, Y), (fun _ => EF.const (-c), X)] with hterms
  have h := expect_deferred_asympEq_zero_of_slack (P := P) (DP := DP) f hf
    (c₀ := fun _ => EF.const 0) (constWeighting 0) (terms := terms)
    (fun p hp => by
      simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact constWeighting 1
      · exact constWeighting (-c))
    (fun p hp => by
      simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hY
      · exact hX)
    (fun p hp => by
      simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hYv
      · exact hXv)
    (B := 1 + |(c : ℝ)|) (by positivity)
    (fun m => by simp [hterms, EF.denote_const])
    slack hslack
    (fun n v hv ν hν => by
      have hνY := hν (fun _ => EF.const 1, Y) (by simp [hterms])
      have hνX := hν (fun _ => EF.const (-c), X) (by simp [hterms])
      obtain ⟨x, hx⟩ := hXv n v hv
      obtain ⟨z, hz, hb⟩ := hr n v hv x hx
      have e1 : ν (Y n) = z := (hνY.eq hz)
      have e2 : ν (X n) = x := (hνX.eq hx)
      simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        EF.denote_const, e1, e2]
      push_cast
      have : (0 : ℝ) + (1 * z + (-(c : ℝ) * x + 0)) = z - (c : ℝ) * x := by ring
      rw [this]
      exact hb) hworld
  have hE : deferredExpect P f (fun _ => EF.const 0) terms =
      fun n => (Y n).expect P (f n) - (c : ℝ) * (X n).expect P (f n) := by
    funext n
    simp only [deferredExpect, hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      EF.denote_const]
    push_cast
    ring
  rw [hE] at h
  unfold AsympEq at h ⊢
  simpa using h

/-- **Deferred-day provind, constant form**: a LUV valued within a vanishing slack of the
constant `b` in every world has `(fun n => (Y n).expect P (f n)) ≈ₙ b`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a); `hf` -/
theorem expect_deferred_const (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f)
    (b : ℚ) {Y : ℕ → LUV} (hY : LUV.MachineThresholdCodeSeq Y) (slack : ℕ → ℝ)
    (hslack : Tendsto slack atTop (𝓝 0))
    (hr : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ z, v.ValuesAt (Y n) z ∧ |z - (b : ℝ)| ≤ slack n)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (Y n).expect P (f n)) ≈ₙ (fun _ => (b : ℝ)) := by
  have hYv : Valued DP Y := fun n v hv => by
    obtain ⟨z, hz, -⟩ := hr n v hv
    exact ⟨z, hz⟩
  set terms : List ((ℕ → EF) × (ℕ → LUV)) := [(fun _ => EF.const 1, Y)] with hterms
  have h := expect_deferred_asympEq_zero_of_slack (P := P) (DP := DP) f hf
    (c₀ := fun _ => EF.const (-b)) (constWeighting (-b)) (terms := terms)
    (fun p hp => by
      simp only [hterms, List.mem_singleton] at hp; subst hp; exact constWeighting 1)
    (fun p hp => by simp only [hterms, List.mem_singleton] at hp; subst hp; exact hY)
    (fun p hp => by simp only [hterms, List.mem_singleton] at hp; subst hp; exact hYv)
    (B := 1 + |(b : ℝ)|) (by positivity)
    (fun m => by simp [hterms, EF.denote_const]; try linarith [abs_nonneg (b : ℝ)])
    slack hslack
    (fun n v hv ν hν => by
      have hνY := hν (fun _ => EF.const 1, Y) (by simp [hterms])
      obtain ⟨z, hz, hb⟩ := hr n v hv
      have e1 : ν (Y n) = z := (hνY.eq hz)
      simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        EF.denote_const, e1]
      push_cast
      have : -(b : ℝ) + (1 * z + 0) = z - (b : ℝ) := by ring
      rw [this]
      exact hb) hworld
  have hE : deferredExpect P f (fun _ => EF.const (-b)) terms =
      fun n => (Y n).expect P (f n) - (b : ℝ) := by
    funext n
    simp only [deferredExpect, hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      EF.denote_const]
    push_cast
    ring
  rw [hE] at h
  unfold AsympEq at h ⊢
  simpa using h

/-- **Deferred-day coherence of a sentence and its negation**:
`P_{f n}(χ_n) + P_{f n}(∼χ_n) ≈ₙ 1` (deferred provind on the literal indicators, whose world
values are the complementary payouts and whose expectations are the prices exactly).
Source: none: infrastructure (li-diagonal's `neg_coherence` at the deferred day)
Kind: L
Fidelity: n/a
Hyps: (a); `hf` -/
theorem deferred_neg_coherence (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f)
    {χ : ℕ → Sentence} (hχ : MachineSentenceCodes χ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P (f n) (χ n) + P (f n) (∼ χ n)) ≈ₙ (fun _ => (1 : ℝ)) := by
  set terms : List ((ℕ → EF) × (ℕ → LUV)) :=
    [(fun _ => EF.const 1, fun n => literalIndicator (χ n)),
      (fun _ => EF.const 1, fun n => literalIndicator (∼ χ n))] with hterms
  have hcodes1 : LUV.MachineThresholdCodeSeq (fun n => literalIndicator (χ n)) :=
    literalIndicator_machineThresholdCodeSeq hχ
  have hcodes2 : LUV.MachineThresholdCodeSeq (fun n => literalIndicator (∼ χ n)) :=
    literalIndicator_machineThresholdCodeSeq hχ.neg
  have h := expect_deferred_asympEq_zero_of_slack (P := P) (DP := DP) f hf
    (c₀ := fun _ => EF.const (-1)) (constWeighting (-1)) (terms := terms)
    (fun p hp => by
      simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact constWeighting 1)
    (fun p hp => by
      simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hcodes1
      · exact hcodes2)
    (fun p hp => by
      simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact fun n v hv => ⟨_, literalIndicator_valuesAt (χ n) DP hv⟩
      · exact fun n v hv => ⟨_, literalIndicator_valuesAt (∼ χ n) DP hv⟩)
    (B := 3) (by norm_num)
    (fun m => by simp [hterms, EF.denote_const]; try norm_num)
    (fun _ => 0) tendsto_const_nhds
    (fun n v hv ν hν => by
      have h1 := hν (fun _ => EF.const 1, fun n => literalIndicator (χ n)) (by simp [hterms])
      have h2 := hν (fun _ => EF.const 1, fun n => literalIndicator (∼ χ n)) (by simp [hterms])
      have e1 := h1.eq (literalIndicator_valuesAt (χ n) DP hv)
      have e2 := h2.eq (literalIndicator_valuesAt (∼ χ n) DP hv)
      simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        EF.denote_const, e1, e2]
      unfold PCWorld.payout
      rw [PCWorld.holds_neg]
      by_cases hχv : v.Holds (χ n) <;> simp [hχv]) hworld
  have hE : deferredExpect P f (fun _ => EF.const (-1)) terms =
      fun n => (P (f n) (χ n) + P (f n) (∼ χ n)) - 1 := by
    funext n
    simp only [deferredExpect, hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      EF.denote_const, literalIndicator_expect]
    push_cast
    ring
  rw [hE] at h
  unfold AsympEq at h ⊢
  simpa using h

end Deferred

end

end Cleanroom.Deference.DefArgmaxValue
