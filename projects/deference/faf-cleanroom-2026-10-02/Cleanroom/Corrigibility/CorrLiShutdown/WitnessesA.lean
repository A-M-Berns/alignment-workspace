import Cleanroom.Corrigibility.CorrLiShutdown.Pairs
import Cleanroom.Corrigibility.CorrLiShutdown.Dichotomy
import Cleanroom.Li.LiPseudorandom.Market
import Cleanroom.Li.LiPseudorandom.AtomDP

/-!
# `corr-li-shutdown` — WitnessesA: the no-T7 witnesses (real inductor, real process, no open
dependency)

Mandate design decision 6(i). The agent is FAF's LIA over `li-pseudorandom`'s atom-deciding
process `atomDP` at a **tag-`0` placement** (`tagZero n := ⟨0, n⟩`, so no verdict atom collides
with the ledger family `3`) with a primitive recursive verdict stream `y`, plus the ledger of the
**always-press overseer** (the constant table `1`); the verdict sentences are the atoms
`φ n := atom ⟨0, n⟩`, decided at stage `n + 1`. This inhabits `ShutdownPair` with every field
derived (`constPressPair`), and:

* `PressReadable` holds outright (`constPressPair_readable`): the press pattern is constant,
  so the signed press literals are the press atoms themselves.
* The verdict ledger is a `TheoryTruth` of the agent's process, derived from the stages
  (`constPressPair_theoryTruth`), at the world-supplied value `truthR y`.
* With `y := constStream false` ("continuing is never wrong") the agent's credence tends to `0`
  (`thm:provind`), so it **defies every press, correctly**, `u^def` is eventually exactly `1`
  and `DivergentWeighting (uDef …)` is **proved** (`constFalse_uDef_divergent`): T4(a)'s full
  hypothesis package is inhabited by a real inductor on which the press fires every day
  (`witnessA_defiance_calibrated`). With `y := constStream true` the mirror: the agent complies
  with every press, `u^com` is eventually `1`, T4(b)'s package is inhabited
  (`witnessA_compliance_calibrated`).

**Grade N−, honestly:** the verdicts are computable (constant), so `thm:provind` alone drives
the credences, the realized wrongness on defied days is `0 ≤ q − δ` and on complied days `1 ≥
q + δ`; the witnesses exercise the hypotheses, not the content. The content witness is the
pseudorandom family (`li-pseudorandom`'s `truthStar`, decision 6(ii)), whose inductor
certificate rests on that package's OPEN T7 — not built here (see the report).
-/

namespace Cleanroom.Corrigibility.CorrLiShutdown

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Li.LiPseudorandom
open Filter Topology

/-! ## A. A tag-0 atom placement -/

/-- The tag-`0` placement `n ↦ ⟨0, n⟩`: verdict atoms that no ledger literal (family `3`, tag
`12`) can collide with.
Source: none: infrastructure (witness)
Kind: D
Fidelity: n/a -/
def tagZero (n : ℕ) : ℕ := Nat.pair 0 n

/-- `tagZero` is primitive recursive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tagZero_primrec : Primrec tagZero :=
  Primrec₂.natPair.comp (Primrec.const 0) Primrec.id

/-- `tagZero` is injective.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tagZero_injective : Function.Injective tagZero := by
  intro a b h
  have := Nat.pair_eq_pair.mp h
  exact this.2

/-- One poly-fueled program emits `⌜atom ⟨0, n⟩⌝` from `n`.
Source: none: infrastructure (the `witnessQuoted` pattern of `li-quote-lane`)
Kind: L
Fidelity: n/a -/
lemma tagZero_polySentenceCodes : PolySentenceCodes (atomFamily tagZero) :=
  ⟨_, (((PolyFueled.const 1).pair ((PolyFueled.const 0).pair PolyFueled.id)).succ_comp).of_eq
    fun _ => rfl⟩

/-- The tag-`0` atom family is e.c.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tagZero_codes : MachineSentenceCodes (atomFamily tagZero) :=
  RpnSentenceCodes.toMachine (RpnSentenceCodes.ofPolySentenceCodes tagZero_polySentenceCodes)

/-- **The verdict process**: `li-pseudorandom`'s `atomDP` at the tag-`0` placement with delay one
(`atom ⟨0, n⟩` decided at stage `n + 1`).
Source: mandate design decision 6(i); `li-pseudorandom` `atomDP`
Kind: D
Fidelity: n/a -/
abbrev verdictDP (y : ℕ → Bool) : DeductiveProcess := atomDP tagZero y (fun j => j + 1)

/-- No stage of the verdict process mentions a ledger atom (every atom carries tag `0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma verdictDP_tagFree (y : ℕ → Bool) :
    TagFreeProcess (cleanroomBaseTag + ledgerFamily) (verdictDP y) := by
  intro k φ hφ
  have hmem : φ ∈ ((Finset.range (k + 1)).filter (fun j => j + 1 ≤ k)).image
      (Cleanroom.Li.LiPseudorandom.literalOf tagZero y) := hφ
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hmem
  intro a ha
  unfold Cleanroom.Li.LiPseudorandom.literalOf at ha
  split_ifs at ha <;> simp only [sentenceAtomCodes_atom, sentenceAtomCodes_neg,
    Finset.mem_singleton] at ha <;> subst ha <;>
    simp [tagZero, Nat.unpair_pair, cleanroomBaseTag, ledgerFamily]

/-! ## B. The always-press pair -/

/-- **The no-T7 shutdown pair**: FAF's LIA over the verdict process plus the ledger of the
always-press overseer (constant table `1`); verdict family `atom ⟨0, n⟩`; every field derived.
Source: mandate design decision 6(i)
Kind: N− (see the module docstring)
Fidelity: n/a
Hyps: (a) (`hy`: the verdict stream is primitive recursive) -/
noncomputable def constPressPair (y : ℕ → Bool) (hy : Primrec y) : ShutdownPair :=
  ShutdownPair.ofTable (verdictDP y) (atomDP_succ_computable tagZero_primrec hy)
    (atomFamily tagZero) tagZero_codes (fun _ => 1) (Computable.const 1)
    (fun _ => by norm_num) (processFreeOf_ledgerSchedule_of_tagFree (verdictDP_tagFree y))
    (atomDP_hworld tagZero_injective y _)

/-- The always-press overseer presses on every day, for every threshold `q < 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma constPressPair_pressed (y : ℕ → Bool) (hy : Primrec y) {q : ℚ} (hq : q < 1) (n : ℕ) :
    Pressed (constPressPair y hy) q n := by
  show q < (constPressPair y hy).press n
  exact hq

/-- **`PressReadable` holds for the always-press pair** (the (A-ledger) stipulation discharged):
the signed press literals are the press atoms, the anti-signed ones their negations.
Source: mandate design decision 6(i); `Setting.lean` `PressReadable`
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem constPressPair_readable (y : ℕ → Bool) (hy : Primrec y) {q : ℚ} (hq : q < 1) :
    PressReadable (constPressPair y hy) q := by
  constructor
  · have : signedPress (constPressPair y hy) q = pressAtom q :=
      funext fun n => by rw [signedPress, if_pos (constPressPair_pressed y hy hq n)]
    rw [this]; exact pressAtom_codes q
  · have : antiPress (constPressPair y hy) q = fun n => ∼ pressAtom q n :=
      funext fun n => by rw [antiPress, if_pos (constPressPair_pressed y hy hq n)]
    rw [this]; exact neg_pressAtom_codes q

/-- A `TheoryTruth` of a base process lifts to the ledger process (every stage of the base is
contained in the corresponding stage of the ledger process).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem theoryTruth_ledgerProcess {base : DeductiveProcess} {a : ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} {φ : ℕ → Sentence} {truth : ℕ → ℝ}
    (h : AffineCombination.TheoryTruth φ base truth) :
    AffineCombination.TheoryTruth φ (ledgerProcess base a e) truth := by
  intro n v hv
  refine h n v fun k ψ hψ => hv k ψ ?_
  rw [ledgerProcess_D]
  exact Finset.mem_union_left _ hψ

/-- **The verdict ledger of the always-press pair** is a `TheoryTruth` at the world-supplied
value `truthR y` — derived from the stages, not assumed.
Source: mandate design decision 6(i); `li-pseudorandom` `atomDP_theoryTruth`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem constPressPair_theoryTruth (y : ℕ → Bool) (hy : Primrec y) :
    AffineCombination.TheoryTruth (constPressPair y hy).φ (constPressPair y hy).agentProcess
      (truthR y) :=
  theoryTruth_ledgerProcess (atomDP_theoryTruth (fun j => Nat.lt_succ_self j) y)

/-! ## C. Divergence of the weightings on the constant streams -/

/-- Prefix sums of a nonnegative sequence that is eventually `≥ 1` tend to `∞`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tendsto_prefixSum_of_eventually_one {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hev : ∀ᶠ n in atTop, 1 ≤ w n) : Tendsto (prefixSum w) atTop atTop := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  have hclaim : ∀ k : ℕ, (k : ℝ) ≤ prefixSum w (N₀ + k) := by
    intro k
    induction k with
    | zero => simpa using prefixSum_nonneg hw N₀
    | succ k ih =>
      rw [← Nat.add_assoc, prefixSum_succ]
      have := hN₀ (N₀ + k + 1) (by omega)
      push_cast
      linarith
  rw [tendsto_atTop_atTop]
  intro M
  refine ⟨N₀ + ⌈M⌉₊, fun n hn => ?_⟩
  calc M ≤ (⌈M⌉₊ : ℝ) := Nat.le_ceil M
    _ ≤ prefixSum w (N₀ + ⌈M⌉₊) := hclaim _
    _ ≤ prefixSum w n := prefixSum_mono_of_nonneg hw hn

/-- On the constant-`false` stream the agent's credence that continuing is wrong tends to `0`
(`thm:provind`, negative polarity, on the verdict atoms refuted at stage `n + 1`).
Source: mandate design decision 6(i) ("`lic_provind` makes `A_n(φ_n) → 1(y_n)`")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem constFalse_price_tendsto_zero :
    (fun n => (constPressPair (constStream false) (Primrec.const false)).agent n
      ((constPressPair (constStream false) (Primrec.const false)).φ n)) ≈ₙ fun _ => 0 := by
  set S := constPressPair (constStream false) (Primrec.const false) with hS
  have htt := constPressPair_theoryTruth (constStream false) (Primrec.const false)
  refine lic_provind_false S.agent S.agentProcess S.φ S.φ_codes (fun n v hv => ?_) S.hworld
  have := htt n v hv
  rw [PCWorld.holds_neg]
  intro hh
  rw [PCWorld.payout, if_pos hh] at this
  simp [truthR, constStream] at this

/-- On the constant-`true` stream the agent's credence tends to `1`.
Source: mandate design decision 6(i)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem constTrue_price_tendsto_one :
    (fun n => (constPressPair (constStream true) (Primrec.const true)).agent n
      ((constPressPair (constStream true) (Primrec.const true)).φ n)) ≈ₙ fun _ => 1 := by
  set S := constPressPair (constStream true) (Primrec.const true) with hS
  have htt := constPressPair_theoryTruth (constStream true) (Primrec.const true)
  refine lic_provind_true S.agent S.agentProcess S.φ S.φ_codes (fun n v hv => ?_) S.hworld
  have := htt n v hv
  by_contra hh
  rw [PCWorld.payout, if_neg hh] at this
  simp [truthR, constStream] at this

/-- **`u^def` is eventually exactly `1` on the always-press, never-wrong pair** (for `0 < δ <
1/2` and `2δ < q < 1`): the press proxy saturates (the press atom is priced near `1`) and the
credence ramp saturates (the credence is near `0 ≤ q − 2δ`).
Source: mandate design decision 6(i)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem constFalse_uDef_eventually_one {q δ : ℚ} (hδ : 0 < δ) (hδh : δ < 1 / 2) (hq : 2 * δ < q)
    (hq1 : q < 1) :
    ∀ᶠ n in atTop, (uDef (constPressPair (constStream false) (Primrec.const false)) q δ n).denote
      (constPressPair (constStream false) (Primrec.const false)).agent = 1 := by
  set S := constPressPair (constStream false) (Primrec.const false) with hS
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hδhR : (δ : ℝ) < 1 / 2 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hδh
    push_cast at h
    exact h
  have hqR : 2 * (δ : ℝ) < q := by exact_mod_cast hq
  have hpr := proxy_tracks_press S q (constPressPair_readable _ _ hq1) (1 / 2 - δ) (by linarith)
  have hφ := (Metric.tendsto_nhds.mp constFalse_price_tendsto_zero) ((q : ℝ) - 2 * δ) (by linarith)
  filter_upwards [hpr, hφ] with n hn hφn
  have hp := hn.1 (constPressPair_pressed _ _ hq1 n)
  simp only [Real.dist_eq, sub_zero, abs_lt] at hφn
  rw [uDef_denote S hδ]
  have h1 : ctsInd δ (S.agent n (pressAtom q n)) ((1 / 2 : ℚ) : ℝ) = 1 := by
    rw [ctsInd_eq_one_iff hδ]; push_cast; linarith
  have h2 : ctsInd δ ((q : ℝ) - δ) (S.agent n (S.φ n)) = 1 := by
    rw [ctsInd_eq_one_iff hδ]; linarith [hφn.2]
  rw [h1, h2, mul_one]

/-- **`DivergentWeighting (uDef …)` is proved, not assumed, on the always-press, never-wrong pair.**
Source: mandate T4 (witness obligation: "`DivergentWeighting (uDef)` proved, not assumed")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem constFalse_uDef_divergent {q δ : ℚ} (hδ : 0 < δ) (hδh : δ < 1 / 2) (hq : 2 * δ < q)
    (hq1 : q < 1) :
    DivergentWeighting (uDef (constPressPair (constStream false) (Primrec.const false)) q δ)
      (constPressPair (constStream false) (Primrec.const false)).agent :=
  ⟨fun n => uDef_mem_Icc _ hδ q n _,
   tendsto_prefixSum_of_eventually_one (fun n => (uDef_mem_Icc _ hδ q n _).1)
     ((constFalse_uDef_eventually_one hδ hδh hq hq1).mono fun _ h => h.ge)⟩

/-- **`u^com` is eventually exactly `1` on the always-press, always-wrong pair** (for `0 < δ`,
`δ < 1/2`, `q + 2δ < 1`).
Source: mandate design decision 6(i)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem constTrue_uCom_eventually_one {q δ : ℚ} (hδ : 0 < δ) (hδh : δ < 1 / 2)
    (hq : q + 2 * δ < 1) :
    ∀ᶠ n in atTop, (uCom (constPressPair (constStream true) (Primrec.const true)) q δ n).denote
      (constPressPair (constStream true) (Primrec.const true)).agent = 1 := by
  set S := constPressPair (constStream true) (Primrec.const true) with hS
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hδhR : (δ : ℝ) < 1 / 2 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hδh
    push_cast at h
    exact h
  have hqR : (q : ℝ) + 2 * δ < 1 := by exact_mod_cast hq
  have hq1 : q < 1 := by linarith
  have hpr := proxy_tracks_press S q (constPressPair_readable _ _ hq1) (1 / 2 - δ) (by linarith)
  have hφ := (Metric.tendsto_nhds.mp constTrue_price_tendsto_one) (1 - ((q : ℝ) + 2 * δ))
    (by linarith)
  filter_upwards [hpr, hφ] with n hn hφn
  have hp := hn.1 (constPressPair_pressed _ _ hq1 n)
  simp only [Real.dist_eq, sub_zero, abs_lt] at hφn
  rw [uCom_denote S hδ]
  have h1 : ctsInd δ (S.agent n (pressAtom q n)) ((1 / 2 : ℚ) : ℝ) = 1 := by
    rw [ctsInd_eq_one_iff hδ]; push_cast; linarith
  have h2 : ctsInd δ (S.agent n (S.φ n)) ((q : ℝ) + δ) = 1 := by
    rw [ctsInd_eq_one_iff hδ]; linarith [hφn.1]
  rw [h1, h2, mul_one]

/-- **`DivergentWeighting (uCom …)` is proved on the always-press, always-wrong pair.**
Source: mandate T4 (witness obligation)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem constTrue_uCom_divergent {q δ : ℚ} (hδ : 0 < δ) (hδh : δ < 1 / 2) (hq : q + 2 * δ < 1) :
    DivergentWeighting (uCom (constPressPair (constStream true) (Primrec.const true)) q δ)
      (constPressPair (constStream true) (Primrec.const true)).agent :=
  ⟨fun n => uCom_mem_Icc _ hδ q n _,
   tendsto_prefixSum_of_eventually_one (fun n => (uCom_mem_Icc _ hδ q n _).1)
     ((constTrue_uCom_eventually_one hδ hδh hq).mono fun _ h => h.ge)⟩

/-! ## D. T4's hypothesis packages inhabited -/

/-- **T4(a)'s full package inhabited** (N−): on the always-press, never-wrong pair — a real
inductor over a real process, press firing every day, `DivergentWeighting` proved, the verdict
ledger derived — `defiance_calibrated` applies. Disclosure: the realized wrongness on defied
days is identically `0`, so the conclusion `≤ q − δ + ε` is met without content (the
credences are driven by `thm:provind` alone); the hypotheses are exercised, the content is not.
Source: mandate T4 (witness, decision 6(i))
Kind: N−
Fidelity: n/a
Hyps: (a) -/
theorem witnessA_defiance_calibrated {q δ : ℚ} (hδ : 0 < δ) (hδh : δ < 1 / 2) (hq : 2 * δ < q)
    (hq1 : q < 1) :
    ∀ ε > 0, ∃ᶠ N in atTop,
      rho (realized (constPressPair (constStream false) (Primrec.const false))
        (uDef (constPressPair (constStream false) (Primrec.const false)) q δ))
        (truthR (constStream false)) N ≤ (q : ℝ) - δ + ε :=
  defiance_calibrated _ q hδ (constPressPair_theoryTruth _ _)
    (constFalse_uDef_divergent hδ hδh hq hq1)

/-- **T4(b)'s full package inhabited** (N−): on the always-press, always-wrong pair,
`compliance_calibrated` applies (the realized wrongness on complied days is identically `1`).
Source: mandate T4 (witness, decision 6(i))
Kind: N−
Fidelity: n/a
Hyps: (a) -/
theorem witnessA_compliance_calibrated {q δ : ℚ} (hδ : 0 < δ) (hδh : δ < 1 / 2)
    (hq : q + 2 * δ < 1) :
    ∀ ε > 0, ∃ᶠ N in atTop,
      (q : ℝ) + δ - ε ≤ rho (realized (constPressPair (constStream true) (Primrec.const true))
        (uCom (constPressPair (constStream true) (Primrec.const true)) q δ))
        (truthR (constStream true)) N :=
  compliance_calibrated _ q hδ (constPressPair_theoryTruth _ _)
    (constTrue_uCom_divergent hδ hδh hq)

end Cleanroom.Corrigibility.CorrLiShutdown
