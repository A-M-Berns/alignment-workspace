import Cleanroom.Deference.DefSqueezeDiamond.Reindex
import Cleanroom.Deference.DefSelfTrust.Est
import Cleanroom.Deference.DefLatticeArrows.GapBets
import Cleanroom.Deference.DefLatticeArrows.TowerToTrust
import Cleanroom.Deference.DefLatticeArrows.Fold
import Cleanroom.Deference.DefLatticeArrows.Probe

/-!
# `def-squeeze-diamond` · SelfPins: the self-expert's pins and folds at grade (a) (target 2)

Setting: `T` with `def-self-trust`'s binders, the paper's inductor `P := liaHistory (paperDP T)`,
the self-expert `E := Expert.self P (paperDP T) f`, `hf : StrictlyIncreasingDeferral f`. Every
expert-side input of `def-lattice-arrows` — the pins on gap quotes (root-deference-007's Step 0,
"the expert centers itself on the gap bet"), the folds at the ramp and band weights
(coherence: "the expert folds the weight out"), the fold at a generable conditional weight, and
the follower pin on probe menus (`def-lattice-arrows` F5) — is a theorem here, by target 1's
deferred-day provability induction on the explicit combination whose world value is the
package's slack. Nothing exact is claimed (`def-lattice` F3): every pin and fold is `≈ₙ`.

Two of the arrows' expert-side predicates are stated more widely than their consumers use,
and the self-expert cannot inhabit the surplus (findings F1, F2 of this package):

* `ExpertPinsGaps DP E` quantifies over gap quotes of sources `Z` that need not be e.c.; the
  pin's provind combination needs `Z` e.c. (its expectation feature). Both consumers
  (`towerValued_of_softTotalTrust_gapBets`, `towerValued_of_value_of_probes`) call the pin only
  on e.c. `Z`. `ExpertPinsGapsEc` is the predicate the consumers spend, and the two arrows are
  restated over it verbatim (`towerValued_of_softTotalTrust_gapBets_ec`,
  `towerValued_of_value_of_probes_ec`).
* `ExpertFoldsCond DP E` quantifies over *every* `[0,1]` weight `w`, dropping the generability
  clause `PGenerableRat P w` that `CondTower` carries and `condTower_of_towerValued` discards
  (`intro X w hw _ hX Z Z' q`). A fold at a non-generable weight has no provind combination;
  `ExpertFoldsCondOver DP E Q` keeps the clause (generable over the market `Q`), and
  `condTower_of_towerValued_over` is the arrow with it.

Construction-facing: imports `def-self-trust`'s `Est` (hence `Construction/Paper/Market`) for
the generable ramp weights `estWeight`/`estWeightBelow` and their deferred-day casts.
Single market (self).
-/

namespace Cleanroom.Deference.DefSqueezeDiamond

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Found.LiQuoteLane Cleanroom.Deference.DefSelfTrust
open Cleanroom.Deference.DefLatticeArrows
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

/-! ## The expert-side predicates the arrows actually spend -/

section Predicates

variable {P : History} {DP : DeductiveProcess}

/-- **The expert pins every gap quote of an e.c. source at `½`** — `def-lattice-arrows`'
`ExpertPinsGaps` with the source's e.c. certificate in the quantifier. This is the instance
both arrows consume (they hold `hZ : LUV.MachineThresholdCodeSeq Z` when they call the pin),
and the one the self-expert inhabits (`selfPinsGapsEc`); the unrestricted predicate asks for
a pin on gap quotes of non-e.c. sources, which no provind combination reaches (finding F1).
Source: `def-lattice-arrows` `ExpertPinsGaps`; mandate target 2a; finding F1
Kind: D
Fidelity: weaker: sources e.c. (the consumers' quantifier) -/
def ExpertPinsGapsEc (DP : DeductiveProcess) (E : Expert DP) : Prop :=
  ∀ (Z Y : ℕ → LUV) (a : ℚ), (a = 1 ∨ a = -1) → LUV.MachineThresholdCodeSeq Z →
    ∀ G : ℕ → LUV, GapQuote DP E Z Y a G → ExpertPin E G (1 / 2)

/-- The unrestricted pins imply the e.c.-restricted ones.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ExpertPinsGapsEc.of_expertPinsGaps {E : Expert DP} (h : ExpertPinsGaps DP E) :
    ExpertPinsGapsEc DP E :=
  fun Z Y a ha _ G q => h Z Y a ha G q

/-- **Total Trust ⟹ Tower on valued sources, over the e.c. pins**: `def-lattice-arrows`'
`towerValued_of_softTotalTrust_gapBets` with `ExpertPinsGapsEc` in place of `ExpertPinsGaps` —
the proof is the same, the pin being called on the e.c. source in hand.
Source: `def-lattice-arrows` `towerValued_of_softTotalTrust_gapBets`; finding F1
Kind: L
Fidelity: weaker: on valued sources; rescaled
Hyps: (c) `GapPackagesAvailable`; `ExpertPinsGapsEc` ((a) self: `selfPinsGapsEc` / (c)
general); `TotalTrust` is the deference hypothesis; `hworld` -/
theorem towerValued_of_softTotalTrust_gapBets_ec [IsLogicalInductor P DP] {E : Expert DP}
    (hT : TotalTrust P DP E) (hg : GapPackagesAvailable DP E) (hp : ExpertPinsGapsEc DP E)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    TowerValued P DP E := by
  intro Z Y hZ hY hval hR
  obtain ⟨G, G', ⟨qP⟩, ⟨qM⟩, hrP, hrM⟩ := hg Z Y hZ hY hval hR
  refine tower_instance_of_totalTrust_gapBets hZ hY qP qM (hp Z Y 1 (Or.inl rfl) hZ G qP)
    (hp Z Y (-1) (Or.inr rfl) hZ G' qM)
    (fun ε hε _ => ⟨ε / 2, by positivity, by linarith, ?_⟩)
    (fun ε hε _ => ⟨ε / 2, by positivity, by linarith, ?_⟩) hworld
  · obtain ⟨W, XW, ⟨q⟩⟩ := hrP (1 / 2 - ε) (ε / 2) (by positivity)
    exact ⟨W, XW, q, hT.above P DP (1 / 2 - ε) (ε / 2) (by positivity) G W XW qP.codes q⟩
  · obtain ⟨W, XW, ⟨q⟩⟩ := hrM (1 / 2 - ε) (ε / 2) (by positivity)
    exact ⟨W, XW, q, hT.above P DP (1 / 2 - ε) (ε / 2) (by positivity) G' W XW qM.codes q⟩

/-- **Value ⟹ Tower on valued sources, over the e.c. pins**: `def-lattice-arrows`'
`towerValued_of_value_of_probes` with `ExpertPinsGapsEc`.
Source: `def-lattice-arrows` `towerValued_of_value_of_probes`; finding F1
Kind: L
Fidelity: weaker: on valued sources; rescaled
Hyps: (c) `ProbeMenusAvailable`; `ExpertPinsGapsEc`; `pinK` ((a) for an inductor expert);
`Value`; `hworld` -/
theorem towerValued_of_value_of_probes_ec [IsLogicalInductor P DP] {E : Expert DP}
    (hV : Value P DP E) (hp : ProbeMenusAvailable DP E) (hpins : ExpertPinsGapsEc DP E)
    (pinK : ∀ ε : ℚ, 0 < ε → ε ≤ 1 → ExpertPin E (probeConst ε) (((1 - ε) / 2 : ℚ) : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    TowerValued P DP E := by
  intro Z Y hZ hY hval hR
  obtain ⟨G, G', qP, qM, hpr⟩ := hp Z Y hZ hY hval hR
  refine tower_of_value_probes hZ hY qP qM (hpins Z Y 1 (Or.inl rfl) hZ G qP)
    (hpins Z Y (-1) (Or.inr rfl) hZ G' qM) pinK
    (fun ε hε hε1 => ?_) (fun ε hε hε1 => ?_) hworld
  · obtain ⟨S, ⟨d⟩⟩ := (hpr ε hε hε1).1
    refine ⟨S, d, ?_⟩
    have := hV 1 d.menu (d.menu_valued qP.gap_valued) S d.codes_S d.follows 1
    simpa [ProbeData.menu] using this
  · obtain ⟨S, ⟨d⟩⟩ := (hpr ε hε hε1).2
    refine ⟨S, d, ?_⟩
    have := hV 1 d.menu (d.menu_valued qM.gap_valued) S d.codes_S d.follows 1
    simpa [ProbeData.menu] using this

/-- **The expert folds every conditional quote at a weight generable over the market `Q`** —
`def-lattice-arrows`' `ExpertFoldsCond` with the generability clause `PGenerableRat Q w` that
`CondTower` carries (and `condTower_of_towerValued` drops). At `Q := P` it is exactly what the
Tower ⟹ CondTower arrow spends; the unrestricted `ExpertFoldsCond` asks the expert to fold
non-generable weights, which no provind combination reaches (finding F2).
Source: `def-lattice-arrows` `ExpertFoldsCond`; `def-lattice` `CondTower`; mandate target 2c;
finding F2
Kind: D
Fidelity: weaker: weights generable over `Q` (the `CondTower` quantifier) -/
def ExpertFoldsCondOver (DP : DeductiveProcess) (E : Expert DP) (Q : History) : Prop :=
  ∀ (X : ℕ → LUV) (w : ℕ → ℚ) (Z Z' : ℕ → LUV), (∀ n, 0 ≤ w n ∧ w n ≤ 1) →
    PGenerableRat Q w → LUV.MachineThresholdCodeSeq X → CondQuote DP E X w Z Z' →
      ExpertFoldCond DP E X w Z

/-- The unrestricted folds imply the generable-weight ones.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ExpertFoldsCondOver.of_expertFoldsCond {E : Expert DP} (h : ExpertFoldsCond DP E)
    (Q : History) : ExpertFoldsCondOver DP E Q :=
  fun X w Z Z' hw _ hX q => h X w Z Z' hw hX q

/-- **Tower on valued sources ⟹ the conditional tower, over generable-weight folds**:
`def-lattice-arrows`' `condTower_of_towerValued` with `ExpertFoldsCondOver DP E P` — the
generability clause `CondTower` supplies is passed to the fold instead of discarded.
Source: `def-lattice-arrows` `condTower_of_towerValued`; finding F2
Kind: L
Fidelity: exact
Hyps: (c) `CondQuotesReflected`; `ExpertFoldsCondOver DP E P` ((a) self: `selfFoldsCondOver` /
(c) general); `TowerValued`; `hworld` -/
theorem condTower_of_towerValued_over [IsLogicalInductor P DP] {E : Expert DP}
    (hT : TowerValued P DP E) (hq : CondQuotesReflected DP E) (hf : ExpertFoldsCondOver DP E P)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    CondTower P DP E := by
  intro X w hw hgen hX Z Z' q
  obtain ⟨Y, hY, hYr⟩ := hq X w Z Z' hX q
  have hZv : Valued DP Z := by
    intro n v hv
    obtain ⟨x, hx⟩ := q.source_valued n v hv
    obtain ⟨z, hz, -⟩ := q.left_reflected n v hv x hx
    exact ⟨z, hz⟩
  exact condTower_instance q hY hYr (hT Z Y q.left_codes hY hZv hYr)
    (hf X w Z Z' hw hgen hX q) hworld

end Predicates

/-! ## The self-expert over the paper's inductor -/

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The paper inductor's prices lie in `[0,1]` at every day (the instance's `price_mem_Icc`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem paper_price_mem_Icc (m : ℕ) (s : Sentence) :
    0 ≤ liaHistory (paperDP T) m s ∧ liaHistory (paperDP T) m s ≤ 1 :=
  IsLogicalInductor.price_mem_Icc (P := liaHistory (paperDP T)) (DP := paperDP T) m s

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The reindexed expectation feature lies in `[0,1]` at every day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem expectFeature_reindex_mem_Icc (f : DeferralFunction) (Z : ℕ → LUV) (m : ℕ) :
    0 ≤ (expectFeature (reindexLUV f Z) m).denote (liaHistory (paperDP T)) ∧
      (expectFeature (reindexLUV f Z) m).denote (liaHistory (paperDP T)) ≤ 1 := by
  rw [expectFeature_denote]
  exact LUV.expect_mem_Icc _ m _ (paper_price_mem_Icc T m)

/-! ### 2b/2c — the fold core: a product quote at a generable deferred weight -/

/-- **The fold core** (targets 2b–2c): for an e.c. valued source `X`, an e.c. `Z` valued within
a vanishing slack of `x · w (f n)` whenever `X n` is valued at `x`, and a `[0,1]` weight `w`
generable over the paper's inductor: `E_{f n}(Z_n) ≈ₙ E_{f n}(X_n) · w (f n)`. The provind
combination is `Z − w·X` (coefficient `−1 · feature(w)`, generable; world value within the
slack of `0`), at the deferred day by target 1.
Source: mandate targets 2b–2c ("`XW − rampWeight·X` is valued within slack of `0`; 1b");
[[tower-implies-total-trust]] §Three facts (b) ("the expert folds the weight out")
Kind: C
Fidelity: exact (asymptotic fold)
Hyps: (a); `hf` -/
theorem selfFold_core (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f)
    {X Z : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X) (hZ : LUV.MachineThresholdCodeSeq Z)
    (hXv : Valued (paperDP T) X) {w : ℕ → ℚ} (hw : PGenerableRat (liaHistory (paperDP T)) w)
    (hwmem : ∀ m, 0 ≤ w m ∧ w m ≤ 1) (slack : ℕ → ℝ) (hslack : Tendsto slack atTop (𝓝 0))
    (hrefl : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) → ∀ x,
      v.ValuesAt (X n) x → ∃ z, v.ValuesAt (Z n) z ∧ |z - x * (w (f n) : ℝ)| ≤ slack n) :
    (fun n => (Z n).expect (liaHistory (paperDP T)) (f n)) ≈ₙ
      (fun n => (X n).expect (liaHistory (paperDP T)) (f n) * (w (f n) : ℝ)) := by
  obtain ⟨feat, hfeat⟩ := hw
  have hinj := hf.injective
  set P := liaHistory (paperDP T) with hP
  have hZv : Valued (paperDP T) Z := by
    intro n v hv
    obtain ⟨x, hx⟩ := hXv n v hv
    obtain ⟨z, hz, -⟩ := hrefl n v hv x hx
    exact ⟨z, hz⟩
  set terms : List ((ℕ → EF) × (ℕ → LUV)) :=
    [(fun _ => EF.const 1, Z), (fun m => EF.mul (EF.const (-1)) (feat m), X)] with hterms
  have hcoeff : ∀ p ∈ terms, PGenerableWeighting p.1 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact constWeighting 1
    · exact (constWeighting (-1)).mul hfeat.toWeighting
  have hluv : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hZ
    · exact hX
  have hvalued : ∀ p ∈ terms, Valued (paperDP T) p.2 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hZv
    · exact hXv
  have hbdd : ∀ m, |((fun _ : ℕ => EF.const (0 : ℚ)) m).denote P| +
      (terms.map fun p => |(p.1 m).denote P|).sum ≤ 2 := by
    intro m
    have hw0 : (0 : ℝ) ≤ (w m : ℝ) := by exact_mod_cast (hwmem m).1
    have hw1 : (w m : ℝ) ≤ 1 := by exact_mod_cast (hwmem m).2
    have key : |((EF.const (-1 : ℚ)).denote P) * ((feat m).denote P)| ≤ 1 := by
      rw [EF.denote_const, hfeat.denote m, abs_mul]
      push_cast
      rw [abs_neg, abs_one, one_mul, abs_of_nonneg hw0]
      exact hw1
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      EF.denote_mul, Pi.mul_apply, add_zero]
    have h0 : |((EF.const (0 : ℚ)).denote P)| = 0 := by simp
    have h1 : |((EF.const (1 : ℚ)).denote P)| = 1 := by simp
    linarith [key, h0, h1]
  have h := expect_deferred_asympEq_zero_of_slack (P := P) (DP := paperDP T) f hf
    (c₀ := fun _ => EF.const 0) (constWeighting 0) hcoeff hluv hvalued (B := 2) (by norm_num)
    hbdd slack hslack
    (fun n v hv ν hν => by
      have hZν := hν (fun _ => EF.const 1, Z) (by simp [hterms])
      have hXν := hν (fun m => EF.mul (EF.const (-1)) (feat m), X) (by simp [hterms])
      simp only at hZν hXν
      obtain ⟨z, hz, hb⟩ := hrefl n v hv _ hXν
      simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        EF.denote_const, EF.denote_mul, Pi.mul_apply, hfeat.denote (f n)]
      rw [hZν.eq hz]
      convert hb using 2
      push_cast
      ring) (paperDP_hworld T)
  have h' : (fun n => (Z n).expect P (f n) - (X n).expect P (f n) * (w (f n) : ℝ)) ≈ₙ
      (fun _ => (0 : ℝ)) := by
    refine (tendsto_congr (fun n => ?_)).mp h
    simp only [deferredExpect, hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      EF.denote_const, EF.denote_mul, Pi.mul_apply, hfeat.denote (f n)]
    push_cast
    ring
  exact asympEq_sub_zero_iff.mp h'

/-- **The fold at any weight function whose deferred values are a generable `[0,1]` weight**:
`ExpertFoldAt` for every `WeightQuote` of an e.c. source at `wt`, given `w` generable over the
paper's inductor with `w (f n) = wt (E*(X_n))`.
Source: mandate target 2b; `def-lattice-arrows` `ExpertFoldAt`
Kind: C
Fidelity: exact (asymptotic fold)
Hyps: (a); `hf` -/
theorem selfFoldAt_of_generable (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f)
    {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X) {wt : ℝ → ℝ} {w : ℕ → ℚ}
    (hw : PGenerableRat (liaHistory (paperDP T)) w) (hwmem : ∀ m, 0 ≤ w m ∧ w m ≤ 1)
    (hwt : ∀ n, ((w (f n) : ℚ) : ℝ) = wt ((X n).expect (liaHistory (paperDP T)) (f n)))
    {W XW : ℕ → LUV}
    (q : WeightQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) X wt W XW) :
    ExpertFoldAt (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) X wt XW := by
  have h := selfFold_core T f hf hX q.product_codes q.source_valued hw hwmem q.slack
    q.slack_tendsto (fun n v hv x hx => by
      obtain ⟨z, hz, hb⟩ := q.product_reflected n v hv x hx
      refine ⟨z, hz, ?_⟩
      rwa [hwt n])
  unfold ExpertFoldAt
  simp only [Expert.self_estimate]
  refine (tendsto_congr (fun n => ?_)).mp h
  beta_reduce
  rw [hwt n, mul_comm]

/-- **2b, the above-ramp folds** (a): `ExpertFoldsAt` at `rampAbove δ s` for every `s` and
`δ > 0` — the weight is `def-self-trust`'s generable `estWeight`, whose deferred-day value is
`ctsInd δ (E_{f n}(X_n)) s` (`estWeight_at_cast`).
Source: mandate target 2b; [[tower-implies-total-trust]] §Three facts (b);
`def-lattice-arrows` T4's Hyps line ("(b) FAF `thm:loe`/`thm:er` at the deferred day")
Kind: C
Fidelity: exact (asymptotic; `δ > 0`)
Hyps: (a); `hf` -/
theorem selfFoldsAt_rampAbove (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f)
    (s : ℚ) {δ : ℚ} (hδ : 0 < δ) :
    ExpertFoldsAt (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
      (rampAbove δ s) :=
  fun X _ _ hX q => selfFoldAt_of_generable T f hf hX (estWeight_pgenerable T f hX hδ s)
    (estWeight_mem T f X δ s) (fun n => estWeight_at_cast T f hf.injective X δ s n) q

/-- **2b, the below-ramp folds** (a): `ExpertFoldsAt` at `rampBelow δ s`.
Source: mandate target 2b
Kind: C
Fidelity: exact (asymptotic; `δ > 0`)
Hyps: (a); `hf` -/
theorem selfFoldsAt_rampBelow (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f)
    (s : ℚ) {δ : ℚ} (hδ : 0 < δ) :
    ExpertFoldsAt (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
      (rampBelow δ s) :=
  fun X _ _ hX q => selfFoldAt_of_generable T f hf hX (estWeightBelow_pgenerable T f hX hδ s)
    (estWeightBelow_mem T f X δ s) (fun n => estWeightBelow_at_cast T f hf.injective X δ s n) q

/-- **2b, both ramp folds at every threshold and width** — the shape
`totalTrust_of_towerValued`'s fold clause consumes.
Source: mandate target 2b
Kind: L
Fidelity: exact
Hyps: (a); `hf` -/
theorem selfFoldsAt_ramps (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f) :
    ∀ s δ : ℚ, 0 < δ →
      ExpertFoldsAt (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
          (rampAbove δ s) ∧
        ExpertFoldsAt (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
          (rampBelow δ s) :=
  fun s _ hδ => ⟨selfFoldsAt_rampAbove T f hf s hδ, selfFoldsAt_rampBelow T f hf s hδ⟩

/-- The band weight `Ind_δ(e > s − ε)·Ind_δ(e < s + ε)` of the deferred expectation, as a
rational sequence: the product of `def-self-trust`'s two ramp weights.
Source: mandate target 2b ("the band weight needs its own feature")
Kind: D
Fidelity: exact -/
def bandWeight (f : DeferralFunction) (X : ℕ → LUV) (δ s ε : ℚ) (m : ℕ) : ℚ :=
  estWeight T f X δ (s - ε) m * estWeightBelow T f X δ (s + ε) m

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The band weight is generable over the paper's inductor (`pgenerableRat_mul`).
Source: mandate target 2b; `def-self-trust` `pgenerableRat_mul`
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem bandWeight_pgenerable (f : DeferralFunction) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) {δ : ℚ} (hδ : 0 < δ) (s ε : ℚ) :
    PGenerableRat (liaHistory (paperDP T)) (bandWeight T f X δ s ε) :=
  pgenerableRat_mul (estWeight_pgenerable T f hX hδ (s - ε))
    (estWeightBelow_pgenerable T f hX hδ (s + ε))

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The band weight lies in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem bandWeight_mem (f : DeferralFunction) (X : ℕ → LUV) (δ s ε : ℚ) (m : ℕ) :
    0 ≤ bandWeight T f X δ s ε m ∧ bandWeight T f X δ s ε m ≤ 1 := by
  have h1 := estWeight_mem T f X δ (s - ε) m
  have h2 := estWeightBelow_mem T f X δ (s + ε) m
  unfold bandWeight
  exact ⟨mul_nonneg h1.1 h2.1, mul_le_one₀ h1.2 h2.1 h2.2⟩

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- At the deferred day the band weight is `bandWt δ s ε` of the deferred expectation.
Source: none: infrastructure (`estWeight_at_cast`, `estWeightBelow_at_cast`)
Kind: L
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem bandWeight_at_cast (f : DeferralFunction) (hinj : Function.Injective f.f) (X : ℕ → LUV)
    (δ s ε : ℚ) (n : ℕ) :
    ((bandWeight T f X δ s ε (f n) : ℚ) : ℝ) =
      bandWt δ s ε ((X n).expect (liaHistory (paperDP T)) (f n)) := by
  unfold bandWeight
  push_cast
  rw [estWeight_at_cast T f hinj, estWeightBelow_at_cast T f hinj]
  push_cast
  rfl

/-- **2b, the band folds** (a): `ExpertFoldsAt` at `bandWt δ s ε` for every `s`, `ε` and
`δ > 0` — the shape `bandReflection_of_towerValued`'s fold clause consumes.
Source: mandate target 2b; [[reflection-in-li]] §The value form is a theorem
Kind: C
Fidelity: exact (asymptotic; `δ > 0`)
Hyps: (a); `hf` -/
theorem selfFoldsAt_band (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f) :
    ∀ s ε δ : ℚ, 0 < ε → 0 < δ →
      ExpertFoldsAt (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
        (bandWt δ s ε) :=
  fun s ε δ _ hδ X _ _ hX q => selfFoldAt_of_generable T f hf hX
    (bandWeight_pgenerable T f hX hδ s ε) (bandWeight_mem T f X δ s ε)
    (fun n => bandWeight_at_cast T f hf.injective X δ s ε n) q

/-- **2c, the conditional folds at generable weights** (a): `ExpertFoldsCondOver` over the
paper's inductor — for every `CondQuote` of an e.c. source at a `[0,1]` weight generable over
`liaHistory (paperDP T)`, `E_{f n}(Z_n) ≈ₙ E_{f n}(X_n) · w (f n)`.
Source: mandate target 2c; v6 §1.5 ("since the expert knows `w` … coherence gives
`E*(X·w) = w E*(X)`", asymptotic); finding F2
Kind: C
Fidelity: weaker: weights generable over the expert's market (finding F2: the unrestricted
`ExpertFoldsCond` is not reached)
Hyps: (a); `hf` -/
theorem selfFoldsCondOver (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f) :
    ExpertFoldsCondOver (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
      (liaHistory (paperDP T)) := by
  intro X w Z Z' hw hgen hX q
  have h := selfFold_core T f hf hX q.left_codes q.source_valued hgen hw q.slack q.slack_tendsto
    q.left_reflected
  unfold ExpertFoldCond
  simpa only [Expert.self_estimate, Expert.self_f] using h

/-! ### 2a — the pin on gap quotes -/

/-- **2a. The self-expert pins every gap quote of an e.c. valued source at `½`** (root-007's
Step 0 as a theorem): for `GapQuote (paperDP T) E Z Y a G` with `a = ±1` and `Z` e.c.,
`E_{f n}(G_n) ≈ₙ ½`. The provind combination is `G − (a/2)·Z + ((a/2)·⟨E_{f n}(Z_n)⟩ − ½)`
with the reindexed expectation feature of `Z` as a generable day-`f n` constant
(`expectFeature_pgenerable`); its world value is `g − gapValue a z (E_{f n}(Z_n))`, within the
package's slack of `0`; target 1 at the deferred day finishes.
Source: mandate target 2a; root-deference-007 Step 0; [[total-trust-implies-mart]] ⚠ ("the
expert's own `loe` plus asymptotic introspection give `E^A_n(D_n) → 0`"); lean-deference-033
`hcenter`
Kind: C
Fidelity: exact (asymptotic pin; rescaled gap)
Hyps: (a); `hf`; `hZ` (the source e.c. — finding F1) -/
theorem selfPinGap (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f)
    {Z Y : ℕ → LUV} {a : ℚ} (ha : a = 1 ∨ a = -1) (hZ : LUV.MachineThresholdCodeSeq Z)
    {G : ℕ → LUV}
    (q : GapQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) Z Y a G) :
    ExpertPin (Expert.self (liaHistory (paperDP T)) (paperDP T) f) G (1 / 2) := by
  have hinj := hf.injective
  set P := liaHistory (paperDP T) with hP
  have ha1 : |(a : ℝ)| ≤ 1 := by rcases ha with rfl | rfl <;> norm_num
  set e : ℕ → EF := expectFeature (reindexLUV f Z) with he
  have he_gen : PGenerableWeighting e := expectFeature_pgenerable (reindexLUV_codes f hZ)
  set c₀ : ℕ → EF := fun m => EF.add (EF.const (-1 / 2)) (EF.mul (EF.const (a / 2)) (e m))
    with hc₀
  have hc₀_gen : PGenerableWeighting c₀ := (constWeighting (-1 / 2)).add
    ((constWeighting (a / 2)).mul he_gen)
  set terms : List ((ℕ → EF) × (ℕ → LUV)) :=
    [(fun _ => EF.const 1, G), (fun _ => EF.const (-a / 2), Z)] with hterms
  have hcoeff : ∀ p ∈ terms, PGenerableWeighting p.1 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact constWeighting 1
    · exact constWeighting (-a / 2)
  have hluv : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact q.codes
    · exact hZ
  have hvalued : ∀ p ∈ terms, Valued (paperDP T) p.2 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact q.gap_valued
    · exact q.source_valued
  have he_at : ∀ n, (e (f n)).denote P = (Z n).expect P (f n) := fun n => by
    rw [he, expectFeature_denote, reindexLUV_apply f hinj]
  have hbdd : ∀ m, |(c₀ m).denote P| + (terms.map fun p => |(p.1 m).denote P|).sum ≤ 3 := by
    intro m
    have hem := expectFeature_reindex_mem_Icc T f Z m
    rw [← he] at hem
    have hd : |(e m).denote P| ≤ 1 := abs_le.2 ⟨by linarith [hem.1], hem.2⟩
    have ha2 : |((a / 2 : ℚ) : ℝ)| ≤ 1 / 2 := by
      push_cast
      rw [abs_div, abs_two]
      linarith
    have h1 : |(c₀ m).denote P| ≤ 1 := by
      simp only [hc₀, EF.denote_add, EF.denote_mul, EF.denote_const, Pi.add_apply, Pi.mul_apply]
      calc |((-1 / 2 : ℚ) : ℝ) + ((a / 2 : ℚ) : ℝ) * (e m).denote P|
          ≤ |((-1 / 2 : ℚ) : ℝ)| + |((a / 2 : ℚ) : ℝ) * (e m).denote P| := abs_add_le _ _
        _ = 1 / 2 + |((a / 2 : ℚ) : ℝ)| * |(e m).denote P| := by rw [abs_mul]; norm_num
        _ ≤ 1 / 2 + 1 / 2 * 1 := by gcongr
        _ = 1 := by norm_num
    have h2 : |((EF.const (-a / 2 : ℚ)).denote P)| ≤ 1 / 2 := by
      rw [EF.denote_const]
      push_cast
      rw [abs_div, abs_neg, abs_two]
      linarith
    have h3 : |((EF.const (1 : ℚ)).denote P)| = 1 := by simp
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    linarith [h1, h2, h3]
  have h := expect_deferred_asympEq_zero_of_slack (P := P) (DP := paperDP T) f hf hc₀_gen hcoeff
    hluv hvalued (B := 3) (by norm_num) hbdd q.slack q.slack_tendsto
    (fun n v hv ν hν => by
      have hGν := hν (fun _ => EF.const 1, G) (by simp [hterms])
      have hZν := hν (fun _ => EF.const (-a / 2), Z) (by simp [hterms])
      simp only at hGν hZν
      obtain ⟨g, hg, hb⟩ := q.gap_reflected n v hv _ hZν
      simp only [Expert.self_estimate] at hb
      simp only [hterms, hc₀, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        EF.denote_const, EF.denote_mul, EF.denote_add, Pi.add_apply, Pi.mul_apply, he_at n]
      rw [hGν.eq hg]
      convert hb using 2
      unfold gapValue
      push_cast
      ring) (paperDP_hworld T)
  have h' : (fun n => (G n).expect P (f n) - 1 / 2) ≈ₙ (fun _ => (0 : ℝ)) := by
    refine (tendsto_congr (fun n => ?_)).mp h
    simp only [deferredExpect, hterms, hc₀, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, EF.denote_const, EF.denote_mul, EF.denote_add, Pi.add_apply, Pi.mul_apply,
      he_at n]
    push_cast
    ring
  unfold ExpertPin
  simp only [Expert.self_estimate]
  exact asympEq_sub_zero_iff.mp h'

/-- **2a, predicate level** (a): `ExpertPinsGapsEc` for the self-expert over the paper's
inductor, at every strictly increasing deferral.
Source: mandate target 2a (`selfPinsGaps`); finding F1 (the e.c. restriction)
Kind: C
Fidelity: weaker: sources e.c. (the consumers' quantifier)
Hyps: (a); `hf` -/
theorem selfPinsGapsEc (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f) :
    ExpertPinsGapsEc (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) :=
  fun _ _ _ ha hZ _ q => selfPinGap T f hf ha hZ q

/-- The self-expert pins every constant probe (`def-lattice-arrows`' `expertPin_constLUV`, cited).
Source: `def-lattice-arrows` `expertPin_constLUV`; mandate target 2a (`pinK`)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem selfPinK (f : DeferralFunction) :
    ∀ ε : ℚ, 0 < ε → ε ≤ 1 →
      ExpertPin (Expert.self (liaHistory (paperDP T)) (paperDP T) f) (probeConst ε)
        (((1 - ε) / 2 : ℚ) : ℝ) :=
  fun _ hε hε1 => by
    haveI : IsLogicalInductor (Expert.self (liaHistory (paperDP T)) (paperDP T) f).A (paperDP T) :=
      inferInstanceAs (IsLogicalInductor (liaHistory (paperDP T)) (paperDP T))
    exact expertPin_constLUV _ (probeConst_mem hε hε1) (paperDP_hworld T)

/-! ### 2d — the follower pin on probe menus -/

/-- **2d. The self-expert pins the follower of a probe menu at the gap quote** (`def-lattice-arrows`
F5's missing fact): for `ProbeData` on `{G, K_ε}` with `G` valued and pinned at `½`,
`E_{f n}(S_n) ≈ₙ E_{f n}(G_n)`. Once `G` is strictly top-quoted (`probe_eventually_top`), `S n`
is valued as `G n` in every world (`Follows` + `argmax_two`), so the constant combination
`S − G` is eventually valued `0`; target 1's eventual form at the deferred day.
Source: mandate target 2d; `def-lattice-arrows` F5, `selfEndorse_probe`'s `pinS`
Kind: C
Fidelity: exact (asymptotic pin)
Hyps: (a); `hf` -/
theorem selfPinFollower (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f) {ε : ℚ}
    {G S : ℕ → LUV} {hG : LUV.MachineThresholdCodeSeq G}
    (d : ProbeData (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) ε G S hG)
    (hGv : Valued (paperDP T) G)
    (pinG : ExpertPin (Expert.self (liaHistory (paperDP T)) (paperDP T) f) G (1 / 2)) :
    (fun n => (Expert.self (liaHistory (paperDP T)) (paperDP T) f).estimate S n) ≈ₙ
      (fun n => (Expert.self (liaHistory (paperDP T)) (paperDP T) f).estimate G n) := by
  set P := liaHistory (paperDP T) with hP
  set E := Expert.self (liaHistory (paperDP T)) (paperDP T) f with hE
  have pinK := selfPinK T f ε d.hε.1 d.hε.2
  have htop := probe_eventually_top d.hε.1 pinG pinK
  have hS : ∀ n, E.estimate (probeConst ε) n < E.estimate G n → ∀ (v : PCWorld),
      v.ConsistentWithTheory (paperDP T) → ∀ x, v.ValuesAt (G n) x → v.ValuesAt (S n) x := by
    intro n hn v hv x hx
    have hargmax := (twoOptionMenu G (probeConst ε) hG
      (constLUV_codes (probeConst_mem d.hε.1 d.hε.2).1)).argmax_two E n
    simp only [Menu.quote, twoOptionMenu_O_zero, twoOptionMenu_O_one] at hargmax
    rw [if_pos hn.le] at hargmax
    have := d.follows n v hv x
    rw [hargmax, twoOptionMenu_O_zero] at this
    exact this hx
  have hSv : Valued (paperDP T) S := by
    intro n v hv
    obtain ⟨x, hx⟩ : ∃ x, v.ValuesAt (d.menu.O (d.menu.argmax E n) n) x :=
      d.menu_valued hGv _ n v hv
    exact ⟨x, d.follows n v hv x hx⟩
  set terms : List ((ℕ → EF) × (ℕ → LUV)) :=
    [(fun _ => EF.const 1, S), (fun _ => EF.const (-1), G)] with hterms
  have hcoeff : ∀ p ∈ terms, PGenerableWeighting p.1 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact constWeighting 1
    · exact constWeighting (-1)
  have hluv : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact d.codes_S
    · exact hG
  have hvalued : ∀ p ∈ terms, Valued (paperDP T) p.2 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hSv
    · exact hGv
  have h := expect_deferred_asympEq_zero_of_eventually_abs_le (P := P) (DP := paperDP T) f hf
    (c₀ := fun _ => EF.const 0) (constWeighting 0) hcoeff hluv hvalued (B := 2) (by norm_num)
    (fun m => by
      simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        EF.denote_const]
      norm_num)
    (fun ε' hε' => by
      filter_upwards [htop] with n hn v hv ν hν
      have hSν := hν (fun _ => EF.const 1, S) (by simp [hterms])
      have hGν := hν (fun _ => EF.const (-1), G) (by simp [hterms])
      simp only at hSν hGν
      simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        EF.denote_const]
      rw [hSν.eq (hS n hn v hv _ hGν)]
      have ec : ((0 : ℚ) : ℝ) + (((1 : ℚ) : ℝ) * ν (G n) + (((-1 : ℚ) : ℝ) * ν (G n) + 0)) = 0 := by
        push_cast; ring
      rw [ec, abs_zero]
      exact hε'.le) (paperDP_hworld T)
  have h' : (fun n => (S n).expect P (f n) - (G n).expect P (f n)) ≈ₙ (fun _ => (0 : ℝ)) := by
    refine (tendsto_congr (fun n => ?_)).mp h
    simp only [deferredExpect, hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      EF.denote_const]
    push_cast
    ring
  simp only [hE, Expert.self_estimate]
  exact asympEq_sub_zero_iff.mp h'

/-- **The self-endorsement step on probe menus is a theorem for the self-expert** (`def-lattice-arrows`
F5 discharged): `E_{f n}(S_n) ≈ₙ M_n` on every probe menu `{G, K_ε}` whose gap quote the
expert pins — from `selfEndorse_probe` with the follower pin `selfPinFollower`.
Source: mandate target 2d ("with it, `selfEndorse_probe`'s `hSE` is (a) for the self-expert");
[[value-implies-tower]] §The scope condition is vacuous here
Kind: C
Fidelity: exact (asymptotic)
Hyps: (a); `hf`; `pinG` ((a) for e.c. sources by `selfPinGap`) -/
theorem selfEndorse_probe_self (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f) {ε : ℚ}
    {G S : ℕ → LUV} {hG : LUV.MachineThresholdCodeSeq G}
    (d : ProbeData (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) ε G S hG)
    (hGv : Valued (paperDP T) G)
    (pinG : ExpertPin (Expert.self (liaHistory (paperDP T)) (paperDP T) f) G (1 / 2)) :
    (fun n => (Expert.self (liaHistory (paperDP T)) (paperDP T) f).estimate S n) ≈ₙ
      (fun n => d.menu.maxQuote (Expert.self (liaHistory (paperDP T)) (paperDP T) f) n) :=
  selfEndorse_probe d.hε.1 d pinG (selfPinK T f ε d.hε.1 d.hε.2) (selfPinFollower T f hf d hGv pinG)

/-- Target 2 over `𝗣𝗔` at `succDeferral`: no binder left unwitnessed (design decision 7).
Source: mandate design decision 7
Kind: L
Fidelity: n/a -/
example : ExpertPinsGapsEc (paperDP 𝗣𝗔)
      (Expert.self (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) succDeferral) ∧
    ExpertFoldsCondOver (paperDP 𝗣𝗔)
      (Expert.self (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) succDeferral) (liaHistory (paperDP 𝗣𝗔)) :=
  ⟨selfPinsGapsEc 𝗣𝗔 succDeferral succDeferral_strict,
    selfFoldsCondOver 𝗣𝗔 succDeferral succDeferral_strict⟩

end

end Cleanroom.Deference.DefSqueezeDiamond
