import Cleanroom.Deference.DefLatticeArrows.Transfer

/-!
# T5 — Total Trust ⟹ Tower by gap-bets on gap-closed classes

Package `def-lattice-arrows`, file 5. [[total-trust-implies-mart]], **at its ⚠ rewrite note**
(the statement of record): bounds transfer (T6) twice at threshold `½` on the two rescaled
gap-bets `G = (Z − ⌜E*(Z)⌝ + 1)/2` and `G' = (⌜E*(Z)⌝ − Z + 1)/2`, whose expert estimates the
expert's own `loe` + introspection pin at `½` (`ExpertPin`, asymptotic — the surrogate
`Γ ⊢ E*(D) = 0` never appears), no `δ`-diagonalization, no provable introspection.

* `expect_gap_pair_asympEq_one`: `G + G'` is valued within slack of `1`, so
  `E^H_n(G_n) + E^H_n(G'_n) ≈ₙ 1`;
* `expect_gap_unfold`: `2G − Z + Y − 1` is valued within slack of `0`, so
  `2E^H_n(G_n) − E^H_n(Z_n) + E^H_n(Y_n) − 1 ≈ₙ 0`;
* `tower_of_gap_halves`: `E^H_n(G_n) ≳ₙ ½` and `E^H_n(G'_n) ≳ₙ ½` give the Tower instance
  `E^H_n(Z_n) ≈ₙ E^H_n(Y_n)` — shared with T11 (`Probe.lean`), where the two lower bounds
  come from Value instead of Total Trust;
* `tower_instance_of_totalTrust_gapBets` (per instance) and
  `towerValued_of_softTotalTrust_gapBets` (predicate level, landing in `TowerValued`).

Only thresholds in `[0, ½)` are used (`½ − ε` for `0 < ε ≤ ½`). The hard form
`HardTotalTrust` is never a hypothesis.
-/

namespace Cleanroom.Deference.DefLatticeArrows

open LogicalInduction Filter Topology Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc

noncomputable section

variable {P : History} {DP : DeductiveProcess}

/-- The two rescaled signed gaps sum to `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gapValue_add_neg (z y : ℝ) : gapValue 1 z y + gapValue (-1) z y = 1 := by
  simp [gapValue]; ring

/-- **The gap pair sums to one**: `E^H_n(G_n) + E^H_n(G'_n) ≈ₙ 1` for a gap quote `G` and its
mirror `G'`, since `G_n + G'_n` is valued within the two slacks of `1` in every consistent
world (T0, slack form).
Source: [[total-trust-implies-mart]] §Proof Step 2 ("The negation `−D` is also in `𝒟`");
[[value-implies-tower]] §Proof Step 4
Kind: C
Fidelity: exact (within slack)
Hyps: (a) -/
theorem expect_gap_pair_asympEq_one [IsLogicalInductor P DP] {E : Expert DP}
    {Z Y G G' : ℕ → LUV} (qP : GapQuote DP E Z Y 1 G) (qM : GapQuote DP E Z Y (-1) G')
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (G n).expect P n + (G' n).expect P n) ≈ₙ (fun _ => (1 : ℝ)) := by
  have h := expect_listComb_eq_of_slack (P := P) (DP := DP) (constStream_splice 0)
    (B := 0) (fun _ => by simp) (ts := [(1, G), (1, G')])
    (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact qP.codes
      · exact qM.codes)
    (listComb_worldValued _ (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · intro n v hv
        obtain ⟨z, hz⟩ := qP.source_valued n v hv
        obtain ⟨g, hg, -⟩ := qP.gap_reflected n v hv z hz
        exact ⟨g, hg⟩
      · intro n v hv
        obtain ⟨z, hz⟩ := qM.source_valued n v hv
        obtain ⟨g, hg, -⟩ := qM.gap_reflected n v hv z hz
        exact ⟨g, hg⟩))
    (1 : ℝ) (slack := fun n => qP.slack n + qM.slack n)
    (by simpa using qP.slack_tendsto.add qM.slack_tendsto)
    (fun n v hv ν hν => by
      obtain ⟨z, hz⟩ := qP.source_valued n v hv
      obtain ⟨g, hg, hgz⟩ := qP.gap_reflected n v hv z hz
      obtain ⟨g', hg', hgz'⟩ := qM.gap_reflected n v hv z hz
      have hGv := listComb_valuesAt_mem hν (p := (1, G)) (by simp)
      have hGv' := listComb_valuesAt_mem hν (p := (1, G')) (by simp)
      rw [listComb_value]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [hGv.eq hg, hGv'.eq hg']
      have hsum := gapValue_add_neg z (E.estimate Z n)
      rw [abs_le] at hgz hgz' ⊢
      push_cast
      constructor <;> linarith [hgz.1, hgz.2, hgz'.1, hgz'.2]) hworld
  refine (tendsto_congr (fun n => ?_)).mp h
  simp [listComb_expect]

/-- **Unfolding the gap**: `2E^H_n(G_n) − E^H_n(Z_n) + E^H_n(Y_n) − 1 ≈ₙ 0` — the combination
`−1 + 2G_n − Z_n + Y_n` is valued within `2·slack n` of `0` (`Y_n` at `E*(Z_n)` by
`Reflects`), and T0 carries it through `E^H_n`. This is the novice's `loe` splitting
`E^H_n(D_n) = E^H_n(Z_n) − E^H_n(⌜E*(Z_n)⌝)`, in the rescaled form.
Source: [[total-trust-implies-mart]] §Proof Step 3 ("`loe` splits"); [[value-implies-tower]]
§Proof Step 5
Kind: C
Fidelity: exact (rescaled; within slack)
Hyps: (a) -/
theorem expect_gap_unfold [IsLogicalInductor P DP] {E : Expert DP} {Z Y G : ℕ → LUV}
    (hZ : LUV.MachineThresholdCodeSeq Z) (hY : LUV.MachineThresholdCodeSeq Y)
    (q : GapQuote DP E Z Y 1 G) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => 2 * (G n).expect P n - (Z n).expect P n + (Y n).expect P n - 1) ≈ₙ
      (fun _ => (0 : ℝ)) := by
  have h := expect_listComb_eq_of_slack (P := P) (DP := DP) (constStream_splice (-1))
    (B := 1) (fun _ => by simp) (ts := [(2, G), (-1, Z), (1, Y)])
    (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact q.codes
      · exact hZ
      · exact hY)
    (listComb_worldValued _ (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · intro n v hv
        obtain ⟨z, hz⟩ := q.source_valued n v hv
        obtain ⟨g, hg, -⟩ := q.gap_reflected n v hv z hz
        exact ⟨g, hg⟩
      · exact q.source_valued
      · exact fun n v hv => ⟨_, q.reflects n v hv⟩))
    (0 : ℝ) (slack := fun n => 2 * q.slack n)
    (by simpa using q.slack_tendsto.const_mul 2)
    (fun n v hv ν hν => by
      obtain ⟨z, hz⟩ := q.source_valued n v hv
      obtain ⟨g, hg, hgz⟩ := q.gap_reflected n v hv z hz
      have hGv := listComb_valuesAt_mem hν (p := (2, G)) (by simp)
      have hZv := listComb_valuesAt_mem hν (p := (-1, Z)) (by simp)
      have hYv := listComb_valuesAt_mem hν (p := (1, Y)) (by simp)
      rw [listComb_value]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [hGv.eq hg, hZv.eq hz, hYv.eq (q.reflects n v hv)]
      simp only [gapValue] at hgz
      rw [abs_le] at hgz ⊢
      push_cast
      constructor <;> linarith [hgz.1, hgz.2]) hworld
  refine (tendsto_congr (fun n => ?_)).mp h
  simp [listComb_expect, sub_eq_add_neg]
  ring

/-- **From the two gap halves to the tower**: `E^H_n(G_n) ≳ₙ ½` and `E^H_n(G'_n) ≳ₙ ½` give
`E^H_n(G_n) ≈ₙ ½` (the pair sums to `1`), hence `E^H_n(Z_n) ≈ₙ E^H_n(Y_n)` (unfolding). The
common last step of T5 (halves from Total Trust) and T11 (halves from Value).
Source: [[total-trust-implies-mart]] §Proof Step 3; [[value-implies-tower]] §Proof Step 5
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem tower_of_gap_halves [IsLogicalInductor P DP] {E : Expert DP} {Z Y G G' : ℕ → LUV}
    (hZ : LUV.MachineThresholdCodeSeq Z) (hY : LUV.MachineThresholdCodeSeq Y)
    (qP : GapQuote DP E Z Y 1 G) (qM : GapQuote DP E Z Y (-1) G')
    (hG : (fun n => (G n).expect P n) ≳ₙ (fun _ => (1 / 2 : ℝ)))
    (hG' : (fun n => (G' n).expect P n) ≳ₙ (fun _ => (1 / 2 : ℝ)))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (Z n).expect P n) ≈ₙ (fun n => (Y n).expect P n) := by
  have hpair := expect_gap_pair_asympEq_one (P := P) qP qM hworld
  have hunf := expect_gap_unfold (P := P) hZ hY qP hworld
  -- `E(G) ≈ₙ ½`
  have hGhalf : (fun n => (G n).expect P n) ≈ₙ (fun _ => (1 / 2 : ℝ)) := by
    rw [asympEq_iff_eventuallyWithin]
    intro ε hε
    filter_upwards [asympEq_eventually_abs_le hpair (half_pos hε), hG' (ε / 2) (half_pos hε),
      hG ε hε] with n h1 h2 h3
    rw [abs_le] at h1 ⊢
    constructor <;> linarith [h1.1, h1.2]
  rw [asympEq_iff_eventuallyWithin]
  intro ε hε
  filter_upwards [asympEq_eventually_abs_le hGhalf (by positivity : (0 : ℝ) < ε / 4),
    asympEq_eventually_abs_le hunf (by positivity : (0 : ℝ) < ε / 2)] with n h1 h2
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Total Trust ⟹ Tower, per instance (T5)**: with a gap quote `G` and its mirror `G'` for
`(Z, Y)`, the expert's pins `E*(G_n) ≈ₙ ½`, `E*(G'_n) ≈ₙ ½`, and the bounds-transfer packages
(a ramp `WeightQuote` at threshold `½ − ε` with its soft Total-Trust instance, for each
`0 < ε ≤ ½`) on `G` and on `G'`: `E^H_n(Z_n) ≈ₙ E^H_n(Y_n)`. Composition: T6 twice at `½`
(`expert_bound_transfer`), then `tower_of_gap_halves`.
Source: [[total-trust-implies-mart]] ⚠ rewrite note (the statement of record: "Lemma 1 of
[[total-trust-implies-value]] applied twice at threshold `0`", rescaled to `½`);
lean-deference-071; vq-wiki-010
Kind: C
Fidelity: variant: rescaled gap-bets in `[0,1]`, threshold `½` in place of `0`; pins
asymptotic
Hyps: (a) the TT instances and the ramp/gap packages (data); (b)/(c) the pins `pinP`, `pinM`
(the expert's `loe` + introspection on the gap: (b) FAF `thm:er` at the deferred day for the
self-expert, (c) general); `hworld` -/
theorem tower_instance_of_totalTrust_gapBets [IsLogicalInductor P DP] {E : Expert DP}
    {Z Y G G' : ℕ → LUV} (hZ : LUV.MachineThresholdCodeSeq Z) (hY : LUV.MachineThresholdCodeSeq Y)
    (qP : GapQuote DP E Z Y 1 G) (qM : GapQuote DP E Z Y (-1) G')
    (pinP : ExpertPin E G (1 / 2)) (pinM : ExpertPin E G' (1 / 2))
    (hpackP : ∀ ε : ℚ, 0 < ε → ε ≤ 1 / 2 → ∃ δ : ℚ, 0 < δ ∧ δ < ε ∧ ∃ W XW : ℕ → LUV,
      ∃ _q : WeightQuote DP E G (rampAbove δ (1 / 2 - ε)) W XW,
        (fun n => (XW n).expect P n - ((1 / 2 - ε : ℚ) : ℝ) * (W n).expect P n) ≳ₙ
          (fun _ => (0 : ℝ)))
    (hpackM : ∀ ε : ℚ, 0 < ε → ε ≤ 1 / 2 → ∃ δ : ℚ, 0 < δ ∧ δ < ε ∧ ∃ W XW : ℕ → LUV,
      ∃ _q : WeightQuote DP E G' (rampAbove δ (1 / 2 - ε)) W XW,
        (fun n => (XW n).expect P n - ((1 / 2 - ε : ℚ) : ℝ) * (W n).expect P n) ≳ₙ
          (fun _ => (0 : ℝ)))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (Z n).expect P n) ≈ₙ (fun n => (Y n).expect P n) := by
  have hAP : (fun n => E.estimate G n) ≳ₙ (fun _ => ((1 / 2 : ℚ) : ℝ)) := by
    push_cast; exact pinP.asympGE
  have hAM : (fun n => E.estimate G' n) ≳ₙ (fun _ => ((1 / 2 : ℚ) : ℝ)) := by
    push_cast; exact pinM.asympGE
  have hG := expert_bound_transfer (P := P) qP.codes (by norm_num : (0 : ℚ) < 1 / 2) hpackP
    hAP hworld
  have hG' := expert_bound_transfer (P := P) qM.codes (by norm_num : (0 : ℚ) < 1 / 2) hpackM
    hAM hworld
  push_cast at hG hG'
  exact tower_of_gap_halves hZ hY qP qM hG hG' hworld

/-- **Gap packages available** — the wiki's "gap-closed class" as an existence clause: for
every e.c. valued `Z` with an e.c. quote `Y`, both rescaled gap quotes exist and their
above-ramp quotes exist. `(c)` for a general expert (`li-quote-lane`); the self-expert's
gap LUVs are `Construction/Quotation` work not done here.
Source: [[total-trust-implies-mart]] §What the theorem costs (H1: gap-closure);
lean-deference-072
Kind: D
Fidelity: exact (an existence clause, disclosed) -/
def GapPackagesAvailable (DP : DeductiveProcess) (E : Expert DP) : Prop :=
  ∀ Z Y : ℕ → LUV, LUV.MachineThresholdCodeSeq Z → LUV.MachineThresholdCodeSeq Y →
    Valued DP Z → Reflects DP E Z Y → ∃ G G' : ℕ → LUV,
      Nonempty (GapQuote DP E Z Y 1 G) ∧ Nonempty (GapQuote DP E Z Y (-1) G') ∧
        RampQuotesAvailable DP E G ∧ RampQuotesAvailable DP E G'

/-- **The expert pins every gap quote at `½`** (the rescaled `E^A_n(±D_n) → 0`): the expert-side
hypothesis of T5 and T11, asymptotic — (b) for the self-expert (FAF `thm:er` at the deferred
day, pull-back not in FAF), (c) in general. Quantified over the two signs the arrows use
(`a = 1`, the gap, and `a = −1`, its mirror) and no others (audit r1 fidelity 4 / adversarial
N6: at `a = 0` the gap LUV is the constant `½` whatever the source, at `|a| > 1` a `GapQuote`
exists only for sources with small gaps — extra signs would make the hypothesis stronger
than T5/T11 consume).
Source: [[total-trust-implies-mart]] ⚠ ("the expert's own `loe` plus asymptotic introspection
give `E^A_n(D_n) → 0`"); [[value-implies-tower]] §Proof Step 1
Kind: D
Fidelity: variant: asymptotic, rescaled -/
def ExpertPinsGaps (DP : DeductiveProcess) (E : Expert DP) : Prop :=
  ∀ (Z Y : ℕ → LUV) (a : ℚ), (a = 1 ∨ a = -1) → ∀ G : ℕ → LUV,
    GapQuote DP E Z Y a G → ExpertPin E G (1 / 2)

/-- **Total Trust ⟹ Tower on valued sources** (predicate level, T5): from `TotalTrust`, the
gap packages and the expert's pins. Lands in `TowerValued` (the gap packages carry
`source_valued`; def-lattice's `Tower` also demands unvalued sources), and is named for
where it lands (the mandate's name `tower_of_softTotalTrust_gapBets` would oversell;
audit r1 fidelity 5).
Source: [[total-trust-implies-mart]] §Statement (over a gap-closed class); vq-wiki-010
Kind: L
Fidelity: weaker: on valued sources; rescaled
Hyps: (c) `GapPackagesAvailable` (existence: the gap-closed class); `ExpertPinsGaps`
((b) self / (c) general); `TotalTrust` is the deference hypothesis; `hworld` -/
theorem towerValued_of_softTotalTrust_gapBets [IsLogicalInductor P DP] {E : Expert DP}
    (hT : TotalTrust P DP E) (hg : GapPackagesAvailable DP E) (hp : ExpertPinsGaps DP E)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    TowerValued P DP E := by
  intro Z Y hZ hY hval hR
  obtain ⟨G, G', ⟨qP⟩, ⟨qM⟩, hrP, hrM⟩ := hg Z Y hZ hY hval hR
  refine tower_instance_of_totalTrust_gapBets hZ hY qP qM (hp Z Y 1 (Or.inl rfl) G qP)
    (hp Z Y (-1) (Or.inr rfl) G' qM)
    (fun ε hε _ => ⟨ε / 2, by positivity, by linarith, ?_⟩)
    (fun ε hε _ => ⟨ε / 2, by positivity, by linarith, ?_⟩) hworld
  · obtain ⟨W, XW, ⟨q⟩⟩ := hrP (1 / 2 - ε) (ε / 2) (by positivity)
    exact ⟨W, XW, q, hT.above P DP (1 / 2 - ε) (ε / 2) (by positivity) G W XW qP.codes q⟩
  · obtain ⟨W, XW, ⟨q⟩⟩ := hrM (1 / 2 - ε) (ε / 2) (by positivity)
    exact ⟨W, XW, q, hT.above P DP (1 / 2 - ε) (ε / 2) (by positivity) G' W XW qM.codes q⟩

end

end Cleanroom.Deference.DefLatticeArrows
