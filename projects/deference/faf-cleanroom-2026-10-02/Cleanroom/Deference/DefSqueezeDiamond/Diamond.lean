import Cleanroom.Deference.DefSqueezeDiamond.PaperExpert
import Cleanroom.Deference.DefLatticeArrows.Hedged
import Cleanroom.Deference.DefLatticeArrows.ArgmaxValue
import Cleanroom.Deference.DefLatticeArrows.Probe
import Cleanroom.Deference.DefLatticeArrows.Fold
import Cleanroom.Deference.DefLatticeArrows.GapBets
import Cleanroom.Deference.DefLatticeArrows.TowerToTrust

/-!
# `def-squeeze-diamond` · Diamond: the closed diamond as one composition (target 5), and the
one-sided self-endorsement step (target 6a)

The corpus's headline ([[centered-bet-squeeze]] §5, root-deference-009): for an observable,
coherent, introspective expert, `Value ⟺ Mart ⟺ Total Trust`. Over FAF, "observable" is the
existence clauses (quotes, product quotes, pinned gap packages, pinned probe menus), "coherent +
introspective" is the pins and folds, and the Value corner is **one-way** (Mart ⟹ Value is
refuted at full menu strength, `def-argmax-value`; it costs the scope condition
`SelfEndorsesGE`). `diamond` is the conjunction, with provenance per arrow in its docstring:

| clause | theorem | clauses spent |
|---|---|---|
| TT ⟹ Tower | `towerValued_of_totalTrust_pinned` (the squeeze, `tower_instance_of_totalTrust_gapBets`) | pinned gap packages |
| Tower ⟹ TT | `totalTrust_of_towerValued` | product quotes, ramp folds |
| Tower ⟹ CondTower | `condTower_of_towerValued_over` | cond quotes, generable-weight folds |
| CondTower ⟹ Tower | `towerValued_of_condTower` | none |
| Value ⟹ Tower | `towerValued_of_value_pinned` (`tower_of_value_probes`) | pinned probe menus, constant pins |
| Tower ∧ SelfEndorsesGE ⟹ Value | `value_of_towerValued_of_selfEndorseGE` | quotes |
| TT ⟹ hedged two-option Value | `hedgedValue_iff_softTotalTrustAbove_instance` | none (the above face restated by definition: `twoOptionComb_expect` + `ring`; not a sixth arrow) |

"All timely" = `≈ₙ`/`≳ₙ` on the same sequence, no limit measure. Every Mart/Tower vertex is
`TowerValued` (design decision 2). **6a**: `SelfEndorsesGE` is the one-sided form of the
arrows' `SelfEndorses` (`≳ₙ` the maximal quote); the arrows' proof spends only
`E*(S_n) ≥ M_n − ε` eventually, so it goes through verbatim
(`value_instance_of_tower_of_selfEndorseGE`, `value_of_towerValued_of_selfEndorseGE`).

Two self-instances. `diamond_self` (5b) proves the five clauses for the self-expert directly:
both sides of every `↔` are theorems (`selfTotalTrust`, `towerValued_self`, `selfCondTower`),
so clauses 1–3 discard their antecedent — a `T`-shaped consistency check of the arrows against
`def-self-trust`'s vertices (design decision 1), not new content, needing no gap or probe
clause. `diamond_self_instance` (`SelfInstance.lean`, repair round 1) is the self-instance *of
the composition*: `diamond` applied with every clause discharged — `pinnedGapPackages_self`,
`pinnedProbeMenus_self` (the mesh gap quotes of `GapMesh` and the probe followers of
`ProbeFollower`), `selfPinK`, the quote packages and the folds. Single market / one-way.
-/

namespace Cleanroom.Deference.DefSqueezeDiamond

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefSelfTrust
open Cleanroom.Deference.DefLatticeArrows Cleanroom.Deference.DefLatticeArrows.Witness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

section General

variable {P : History} {DP : DeductiveProcess}

/-! ## 6a — one-sided self-endorsement suffices -/

/-- **One-sided self-endorsement** (6a): on every e.d. valued menu and every e.d. follower, the
expert's estimate of the follower is asymptotically *at least* its maximal quote — the arrows'
`SelfEndorses` with `≈ₙ` weakened to `≳ₙ`, which is all Mart ⟹ Value spends.
Source: mandate target 6a; [[total-trust-implies-value]] §Lemma 2 ("one-sidedness is
deliberate"); lean-deference-003
Kind: D
Fidelity: weaker: one-sided (the `≲ₙ` half is never used) -/
def SelfEndorsesGE (DP : DeductiveProcess) (E : Expert DP) : Prop :=
  ∀ (k : ℕ) (M : Menu k), M.Valued DP → ∀ S : ℕ → LUV, LUV.MachineThresholdCodeSeq S →
    Follows DP E M S → (fun n => E.estimate S n) ≳ₙ (fun n => M.maxQuote E n)

/-- Two-sided self-endorsement implies the one-sided form.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem SelfEndorsesGE.of_selfEndorses {E : Expert DP} (h : SelfEndorses DP E) :
    SelfEndorsesGE DP E :=
  fun k M hM S hS hF => (h k M hM S hS hF).asympGE

/-- **Tower ⟹ Value per menu instance, under one-sided self-endorsement** (6a): the arrows'
`value_instance_of_tower_of_selfEndorse` with `hSE : E*(S_n) ≳ₙ M_n` — the proof spends only
`M_n ≤ E*(S_n) + ε` eventually.
Source: mandate target 6a; `def-lattice-arrows` `value_instance_of_tower_of_selfEndorse`
Kind: C
Fidelity: variant: one-sided `hSE`
Hyps: (a) the Tower instances and quotes (data); (c) `hSE`; `hworld` -/
theorem value_instance_of_tower_of_selfEndorseGE [IsLogicalInductor P DP] {E : Expert DP}
    {k : ℕ} (M : Menu k) {S YS Yi : ℕ → LUV} (i : Fin (k + 1))
    (hYS : LUV.MachineThresholdCodeSeq YS) (hYi : LUV.MachineThresholdCodeSeq Yi)
    (hRS : Reflects DP E S YS) (hRi : Reflects DP E (M.O i) Yi)
    (hTS : (fun n => (S n).expect P n) ≈ₙ (fun n => (YS n).expect P n))
    (hTi : (fun n => (M.O i n).expect P n) ≈ₙ (fun n => (Yi n).expect P n))
    (hSE : (fun n => E.estimate S n) ≳ₙ (fun n => M.maxQuote E n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (S n).expect P n) ≳ₙ (fun n => (M.O i n).expect P n) := by
  have h := expect_listComb_ge_of_eventually (P := P) (DP := DP) (constStream_splice 0)
    (B := 0) (fun _ => by simp) (ts := [(1, YS), (-1, Yi)])
    (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hYS
      · exact hYi)
    (listComb_worldValued _ (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact fun n v hv => ⟨_, hRS n v hv⟩
      · exact fun n v hv => ⟨_, hRi n v hv⟩))
    (0 : ℝ) (fun ε hε => by
      filter_upwards [hSE ε hε] with n hn v hv ν hν
      have hSv := listComb_valuesAt_mem hν (p := (1, YS)) (by simp)
      have hiv := listComb_valuesAt_mem hν (p := (-1, Yi)) (by simp)
      rw [listComb_value]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [hSv.eq (hRS n v hv), hiv.eq (hRi n v hv)]
      have hmax := M.quote_le_maxQuote E i n
      simp only [Menu.quote] at hmax
      push_cast
      linarith) hworld
  have h0 : (fun n => (Yi n).expect P n) ≲ₙ (fun n => (YS n).expect P n) := by
    intro ε hε
    filter_upwards [h ε hε] with n hn
    simp only [listComb_expect, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hn
    push_cast at hn
    linarith
  exact (hTi.trans_asympLE h0).trans_asympEq hTS.symm

/-- **Tower on valued sources ⟹ Value under one-sided self-endorsement** (6a, predicate level).
Source: mandate target 6a; `def-lattice-arrows` `value_of_towerValued_of_selfEndorse`
Kind: L
Fidelity: variant: under the disclosed one-sided self-endorsement
Hyps: (c) `QuotesAvailable`, `SelfEndorsesGE`; `TowerValued` is the deference hypothesis;
`hworld` -/
theorem value_of_towerValued_of_selfEndorseGE [IsLogicalInductor P DP] {E : Expert DP}
    (hT : TowerValued P DP E) (hq : QuotesAvailable DP E) (hSE : SelfEndorsesGE DP E)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Value P DP E := by
  intro k M hM S hS hF i
  obtain ⟨YS, hYS, hRS⟩ := hq S hS
  obtain ⟨Yi, hYi, hRi⟩ := hq (M.O i) (M.codes i)
  exact value_instance_of_tower_of_selfEndorseGE M i hYS hYi hRS hRi
    (hT S YS hS hYS (follows_valued hM hF) hRS) (hT (M.O i) Yi (M.codes i) hYi (hM i) hRi)
    (hSE k M hM S hS hF) hworld

/-! ## The pinned packages (design decision 4) -/

/-- **Pinned gap packages**: for every e.c. valued source with e.c. quote, both gap quotes exist,
the expert pins them at `½`, and their above-ramp quotes exist — `GapPackagesAvailable` and
the pins in one clause, so that no pin is asked on a gap LUV the expert need not price.
Source: mandate design decision 4; mandate target 5a
Kind: D
Fidelity: exact (an existence clause, disclosed) -/
def PinnedGapPackages (DP : DeductiveProcess) (E : Expert DP) : Prop :=
  ∀ Z Y : ℕ → LUV, LUV.MachineThresholdCodeSeq Z → LUV.MachineThresholdCodeSeq Y →
    Valued DP Z → Reflects DP E Z Y → ∃ G G' : ℕ → LUV,
      ∃ _qP : GapQuote DP E Z Y 1 G, ∃ _qM : GapQuote DP E Z Y (-1) G',
        ExpertPin E G (1 / 2) ∧ ExpertPin E G' (1 / 2) ∧
          RampQuotesAvailable DP E G ∧ RampQuotesAvailable DP E G'

/-- **Pinned probe menus**: both gap quotes, pinned, with probe followers at every margin.
Source: mandate design decision 4; mandate target 5a
Kind: D
Fidelity: exact (an existence clause, disclosed) -/
def PinnedProbeMenus (DP : DeductiveProcess) (E : Expert DP) : Prop :=
  ∀ Z Y : ℕ → LUV, LUV.MachineThresholdCodeSeq Z → LUV.MachineThresholdCodeSeq Y →
    Valued DP Z → Reflects DP E Z Y → ∃ G G' : ℕ → LUV,
      ∃ qP : GapQuote DP E Z Y 1 G, ∃ qM : GapQuote DP E Z Y (-1) G',
        ExpertPin E G (1 / 2) ∧ ExpertPin E G' (1 / 2) ∧
          ∀ ε : ℚ, 0 < ε → ε ≤ 1 →
            (∃ S : ℕ → LUV, Nonempty (ProbeData DP E ε G S qP.codes)) ∧
            (∃ S : ℕ → LUV, Nonempty (ProbeData DP E ε G' S qM.codes))

/-- **Total Trust ⟹ Tower on valued sources, over pinned gap packages** (the squeeze at
predicate level with the pins inside the package).
Source: mandate target 5a; `def-lattice-arrows` `towerValued_of_softTotalTrust_gapBets`
Kind: L
Fidelity: weaker: on valued sources; rescaled
Hyps: (c) `PinnedGapPackages`; `TotalTrust` is the deference hypothesis; `hworld` -/
theorem towerValued_of_totalTrust_pinned [IsLogicalInductor P DP] {E : Expert DP}
    (hT : TotalTrust P DP E) (hg : PinnedGapPackages DP E)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    TowerValued P DP E := by
  intro Z Y hZ hY hval hR
  obtain ⟨G, G', qP, qM, pinP, pinM, hrP, hrM⟩ := hg Z Y hZ hY hval hR
  refine tower_instance_of_totalTrust_gapBets hZ hY qP qM pinP pinM
    (fun ε hε _ => ⟨ε / 2, by positivity, by linarith, ?_⟩)
    (fun ε hε _ => ⟨ε / 2, by positivity, by linarith, ?_⟩) hworld
  · obtain ⟨W, XW, ⟨q⟩⟩ := hrP (1 / 2 - ε) (ε / 2) (by positivity)
    exact ⟨W, XW, q, hT.above P DP (1 / 2 - ε) (ε / 2) (by positivity) G W XW qP.codes q⟩
  · obtain ⟨W, XW, ⟨q⟩⟩ := hrM (1 / 2 - ε) (ε / 2) (by positivity)
    exact ⟨W, XW, q, hT.above P DP (1 / 2 - ε) (ε / 2) (by positivity) G' W XW qM.codes q⟩

/-- **Value ⟹ Tower on valued sources, over pinned probe menus**.
Source: mandate target 5a; `def-lattice-arrows` `towerValued_of_value_of_probes`
Kind: L
Fidelity: weaker: on valued sources; rescaled
Hyps: (c) `PinnedProbeMenus`; `pinK` ((a) for an inductor expert); `Value`; `hworld` -/
theorem towerValued_of_value_pinned [IsLogicalInductor P DP] {E : Expert DP}
    (hV : Value P DP E) (hp : PinnedProbeMenus DP E)
    (pinK : ∀ ε : ℚ, 0 < ε → ε ≤ 1 → ExpertPin E (probeConst ε) (((1 - ε) / 2 : ℚ) : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    TowerValued P DP E := by
  intro Z Y hZ hY hval hR
  obtain ⟨G, G', qP, qM, pinP, pinM, hpr⟩ := hp Z Y hZ hY hval hR
  refine tower_of_value_probes hZ hY qP qM pinP pinM pinK
    (fun ε hε hε1 => ?_) (fun ε hε hε1 => ?_) hworld
  · obtain ⟨S, ⟨d⟩⟩ := (hpr ε hε hε1).1
    refine ⟨S, d, ?_⟩
    have := hV 1 d.menu (d.menu_valued qP.gap_valued) S d.codes_S d.follows 1
    simpa [ProbeData.menu] using this
  · obtain ⟨S, ⟨d⟩⟩ := (hpr ε hε hε1).2
    refine ⟨S, d, ?_⟩
    have := hV 1 d.menu (d.menu_valued qM.gap_valued) S d.codes_S d.follows 1
    simpa [ProbeData.menu] using this

/-! ## 5a — the diamond -/

/-- **The closed diamond, as one composition** (load-bearing 5): for an inductor novice `P`
over `DP` and an expert `E` with the pinned gap packages, the pinned probe menus, the constant
pins, the product quotes and ramp folds at every ramp, the conditional quotes and
generable-weight folds, and the quotes of every e.c. family —
`(TotalTrust ↔ TowerValued) ∧ (TowerValued ↔ CondTower) ∧ (Value → TowerValued) ∧
(TowerValued → SelfEndorsesGE → Value) ∧ (TotalTrust → hedged two-option Value at every ramp
quote)`. Per arrow (see the module table): TT ⟹ Tower is the squeeze
(`towerValued_of_totalTrust_pinned`), Tower ⟹ TT the fold (`totalTrust_of_towerValued`),
Tower ⟺ CondTower the conditional fold and `w ≡ 1` (`condTower_of_towerValued_over`,
`towerValued_of_condTower`), Value ⟹ Tower the probe menus (`towerValued_of_value_pinned`,
no scope condition: probe menus are self-stable), Tower ⟹ Value one-way and `(c)`-labelled
(`value_of_towerValued_of_selfEndorseGE`; refuted without the scope condition,
`def-argmax-value`), TT ⟹ hedged Value the above face restated by definition
(`hedgedValue_iff_softTotalTrustAbove_instance`: `E(twoOptionComb s XW W) = E(XW) + s − s·E(W)`,
so `≳ₙ s` is literally the above face — a clause, not a sixth arrow). Every `≈ₙ`/`≳ₙ` is on
the same sequence. The full hypothesis package is inhabited for the self-expert by
`diamond_self_instance` (`SelfInstance.lean`).
Source: mandate target 5a; root-deference-009 ([[centered-bet-squeeze]] §5); vq-wiki-008(b);
[[value-iff-mart]] ⚠ 2026-07-27 ("six arrows exist; three suffice"); [[loop-direction]]
Kind: C (plumbing over the arrows' theorems; the content is the discharged clauses —
`diamond_self_instance`)
Fidelity: variant: Mart/Tower as `TowerValued`; the Value corner one-way under `SelfEndorsesGE`
Hyps: (c) the existence clauses `hgap`, `hprobe`, `hq`, `hcq`, `hquotes` ((a) self:
`pinnedGapPackages_self`, `pinnedProbeMenus_self`, `paperExpert_productQuotesAvailable`,
`paperExpert_condQuotesReflected`, `quotesAvailable_self`); the folds `hf`, `hfc` ((a) self:
`selfFoldsAt_ramps`, `selfFoldsCondOver` / (c) general); `pinK` ((a) for an inductor expert);
`hworld` -/
theorem diamond [IsLogicalInductor P DP] (E : Expert DP)
    (hgap : PinnedGapPackages DP E) (hprobe : PinnedProbeMenus DP E)
    (pinK : ∀ ε : ℚ, 0 < ε → ε ≤ 1 → ExpertPin E (probeConst ε) (((1 - ε) / 2 : ℚ) : ℝ))
    (hq : ∀ s δ : ℚ, 0 < δ → ProductQuotesAvailable DP E (rampAbove δ s) ∧
      ProductQuotesAvailable DP E (rampBelow δ s))
    (hf : ∀ s δ : ℚ, 0 < δ → ExpertFoldsAt DP E (rampAbove δ s) ∧
      ExpertFoldsAt DP E (rampBelow δ s))
    (hcq : CondQuotesReflected DP E) (hfc : ExpertFoldsCondOver DP E P)
    (hquotes : QuotesAvailable DP E)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (TotalTrust P DP E ↔ TowerValued P DP E) ∧
    (TowerValued P DP E ↔ CondTower P DP E) ∧
    (Value P DP E → TowerValued P DP E) ∧
    (TowerValued P DP E → SelfEndorsesGE DP E → Value P DP E) ∧
    (TotalTrust P DP E → ∀ (s δ : ℚ) (X W XW : ℕ → LUV), 0 < δ →
      LUV.MachineThresholdCodeSeq X → WeightQuote DP E X (rampAbove δ s) W XW →
        (fun n => (twoOptionComb s XW W n).expect P n) ≳ₙ (fun _ => (s : ℝ))) :=
  ⟨⟨fun hT => towerValued_of_totalTrust_pinned hT hgap hworld,
    fun hT => totalTrust_of_towerValued hT hq hf hworld⟩,
   ⟨fun hT => condTower_of_towerValued_over hT hcq hfc hworld, towerValued_of_condTower⟩,
   fun hV => towerValued_of_value_pinned hV hprobe pinK hworld,
   fun hT hSE => value_of_towerValued_of_selfEndorseGE hT hquotes hSE hworld,
   fun hT s δ X W XW hδ hX q =>
     (hedgedValue_iff_softTotalTrustAbove_instance P s XW W).mpr ((hT s δ hδ).1 X W XW hX q)⟩

end General

/-! ## 5b — the self-instance: a consistency check -/

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- **The diamond for the self-expert** (5b): for the self-expert over the paper's inductor both
sides of every `↔` are theorems (`selfTotalTrust`, `towerValued_self`, `selfCondTower`), so the
five clauses hold with no hypothesis — the Value corner through
`value_of_towerValued_of_selfEndorseGE` with `quotesAvailable_self`, the hedged clause through
`selfTotalTrust`. This is a consistency check of the arrows against `def-self-trust`'s
vertices, not new content (design decision 1): clauses 1–3 discard their antecedent
(`fun _ => towerValued_self …`), which is exactly the shape the mandate calls a `T` row; the
instance of the *composition* `diamond` with every clause discharged is
`diamond_self_instance` (`SelfInstance.lean`).
Source: mandate target 5b
Kind: T (consistency check; clauses 1–3 discard the antecedent — audit r1 N3)
Fidelity: exact (the self-expert's vertices are theorems)
Hyps: (a) none; `hf` -/
theorem diamond_self (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f) :
    (TotalTrust (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f) ↔
      TowerValued (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f)) ∧
    (TowerValued (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f) ↔
      CondTower (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f)) ∧
    (Value (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f) →
      TowerValued (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f)) ∧
    (TowerValued (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f) →
      SelfEndorsesGE (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) →
      Value (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f)) ∧
    (∀ (s δ : ℚ) (X W XW : ℕ → LUV), 0 < δ → LUV.MachineThresholdCodeSeq X →
      WeightQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) X
        (rampAbove δ s) W XW →
      (fun n => (twoOptionComb s XW W n).expect (liaHistory (paperDP T)) n) ≳ₙ
        (fun _ => (s : ℝ))) :=
  ⟨⟨fun _ => towerValued_self T f, fun _ => selfTotalTrust T f hf.injective⟩,
   ⟨fun _ => condTower_self_via_arrows T f hf, fun _ => towerValued_self T f⟩,
   fun _ => towerValued_self T f,
   fun hT hSE => value_of_towerValued_of_selfEndorseGE hT (quotesAvailable_self T f) hSE
     (paperDP_hworld T),
   fun s δ X W XW hδ hX q => (hedgedValue_iff_softTotalTrustAbove_instance _ s XW W).mpr
     ((selfTotalTrust T f hf.injective).above _ _ s δ hδ X W XW hX q)⟩

end

end Cleanroom.Deference.DefSqueezeDiamond
