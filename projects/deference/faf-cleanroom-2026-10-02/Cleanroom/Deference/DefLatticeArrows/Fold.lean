import Cleanroom.Deference.DefLatticeArrows.Packages

/-!
# T3 — The ε-fold: the universal tower contains the conditional tower

Package `def-lattice-arrows`, file 4. v6 §1.5 / [[tower-implies-total-trust]] §The other
direction ("the two-sided fold equality") over `def-lattice`'s objects: a `CondQuote`
`(Z, Z')` for the weight `w` (left product `Z` within FAF's slack, right product `Z'` exact,
both at the deferred day `w (E.f n)`), a quote `Y` reflecting `E*(Z)`, the Tower instance at
`Z`, and the expert's asymptotic fold `E*(Z_n) ≈ₙ E*(X_n) · w (f n)` (`ExpertFoldCond`) give
the conditional-tower instance `E^H_n(Z_n) ≈ₙ E^H_n(Z'_n)`.

The introspection input is bound precisely: `ExpertFoldCond` is the *only* expert-side
hypothesis, asymptotic (for the self-expert it is the shape of FAF's `thm:loe`/`thm:er` at the
deferred day, a pull-back FAF does not provide — `(b)`; `(c)` for a general expert). No
`PGenerableRat` is needed at the instance level: the weight's generability lives in
`CondTower`'s quantifier and is consumed only by the predicate-level corollary.

Converse (`towerValued_of_condTower`): `CondTower` at the constant weight `1` recovers the
tower on every *valued* source (`TowerValued`); def-lattice's `Tower` also ranges over
unvalued sources, which `CondQuote.source_valued` excludes, so `Tower ⟺ CondTower` holds on
valued sources only. The arrows' consumers never touch unvalued sources, so nothing
downstream weakens.
-/

namespace Cleanroom.Deference.DefLatticeArrows

open LogicalInduction Filter Topology Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc

noncomputable section

variable {P : History} {DP : DeductiveProcess}

/-- **The conditional tower from one Tower instance, per instance (T3).** Given a `CondQuote`
`(Z, Z')` of `X` at the weight `w`, an e.c. quote `Y` reflecting `E*(Z)`, the Tower instance
`E^H_n(Z_n) ≈ₙ E^H_n(Y_n)` and the expert's fold `E*(Z_n) ≈ₙ E*(X_n)·w(f n)`:
`E^H_n(Z_n) ≈ₙ E^H_n(Z'_n)`. Proof: `Y_n − Z'_n` is valued at `E*(Z_n) − E*(X_n)·w(f n) → 0`;
T0 (`_eq`, eventual) gives `E^H_n(Y_n) ≈ₙ E^H_n(Z'_n)`; chain with the Tower instance.
Source: v6 §1.5 (root-deference-004); [[tower-implies-total-trust]] §The other direction;
lean-deference-009; vq-wiki-003
Kind: C
Fidelity: exact (weight at `w (E.f n)`, def-lattice F2; left product within FAF's slack)
Hyps: (a) the Tower instance `hT` and the package `q` (data); (b)/(c) `hfold` — the expert's
asymptotic fold ((b) self-expert: FAF `thm:loe`/`thm:er` at the deferred day, pull-back not in
FAF; (c) general expert); `hworld` -/
theorem condTower_instance [IsLogicalInductor P DP] {E : Expert DP} {X Z Z' Y : ℕ → LUV}
    {w : ℕ → ℚ} (q : CondQuote DP E X w Z Z') (hY : LUV.MachineThresholdCodeSeq Y)
    (hYr : Reflects DP E Z Y)
    (hT : (fun n => (Z n).expect P n) ≈ₙ (fun n => (Y n).expect P n))
    (hfold : ExpertFoldCond DP E X w Z)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (Z n).expect P n) ≈ₙ (fun n => (Z' n).expect P n) := by
  have h := expect_listComb_eq_of_eventually (P := P) (DP := DP) (constStream_splice 0)
    (B := 0) (fun _ => by simp) (ts := [(1, Y), (-1, Z')])
    (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hY
      · exact q.right_codes)
    (listComb_worldValued _ (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact fun n v hv => ⟨_, hYr n v hv⟩
      · exact fun n v hv => ⟨_, q.right_reflected n v hv⟩))
    (0 : ℝ) (fun ε hε => by
      filter_upwards [asympEq_eventually_abs_le hfold hε] with n hn v hv ν hν
      have hYv := listComb_valuesAt_mem hν (p := (1, Y)) (by simp)
      have hZv := listComb_valuesAt_mem hν (p := (-1, Z')) (by simp)
      rw [listComb_value]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [hYv.eq (hYr n v hv), hZv.eq (q.right_reflected n v hv)]
      have : ((0 : ℚ) : ℝ) + (((1 : ℚ) : ℝ) * E.estimate Z n +
          (((-1 : ℚ) : ℝ) * (E.estimate X n * (w (E.f n) : ℝ)) + 0)) - 0 =
          E.estimate Z n - E.estimate X n * (w (E.f n) : ℝ) := by push_cast; ring
      rw [this]
      exact hn) hworld
  have h' : (fun n => (Y n).expect P n) ≈ₙ (fun n => (Z' n).expect P n) := by
    rw [← asympEq_sub_zero_iff]
    refine (tendsto_congr (fun n => ?_)).mp h
    simp [listComb_expect, sub_eq_add_neg]
  exact hT.trans h'

/-- **Existence of the quote of the left product**: for every `CondQuote` `(Z, Z')` of an e.c.
source at a `[0,1]` P-generable weight, some e.c. `Y` reflects `E*(Z)`. `(c)` for a general
expert; for `Expert.self` FAF's `Construction/Quotation` supplies it (cited, not built).
Source: [[value-implies-tower]] §What the theorem costs ("Channel"); mandate T3
Kind: D
Fidelity: exact (an existence clause, disclosed) -/
def CondQuotesReflected (DP : DeductiveProcess) (E : Expert DP) : Prop :=
  ∀ (X : ℕ → LUV) (w : ℕ → ℚ) (Z Z' : ℕ → LUV), LUV.MachineThresholdCodeSeq X →
    CondQuote DP E X w Z Z' → ∃ Y : ℕ → LUV, LUV.MachineThresholdCodeSeq Y ∧ Reflects DP E Z Y

/-- **The expert folds every conditional quote**: `ExpertFoldCond` for every `CondQuote` of
every e.c. source at every `[0,1]` weight — the ε-fold, asymptotic ((b) self / (c) general).
Source: v6 §1.5 ("since the expert knows `w` … coherence gives `E*(X·w) = w E*(X)`", in the
asymptotic form the grid forces)
Kind: D
Fidelity: variant: asymptotic -/
def ExpertFoldsCond (DP : DeductiveProcess) (E : Expert DP) : Prop :=
  ∀ (X : ℕ → LUV) (w : ℕ → ℚ) (Z Z' : ℕ → LUV), (∀ n, 0 ≤ w n ∧ w n ≤ 1) →
    LUV.MachineThresholdCodeSeq X → CondQuote DP E X w Z Z' → ExpertFoldCond DP E X w Z

/-- **Tower on valued sources ⟹ the conditional tower** (predicate level, T3):
`CondTower P DP E` from `TowerValued`, the quotes of the left products, and the expert's
folds. The left product is valued (`CondQuote.source_valued` + `left_reflected`), so
`TowerValued` suffices.
Source: v6 §1.5; [[deference-notions]] §The conditional tower; vq-wiki-003
Kind: L
Fidelity: exact
Hyps: (c) `CondQuotesReflected` (existence); `ExpertFoldsCond` ((b) self / (c) general);
`TowerValued` is the deference hypothesis; `hworld` -/
theorem condTower_of_towerValued [IsLogicalInductor P DP] {E : Expert DP}
    (hT : TowerValued P DP E) (hq : CondQuotesReflected DP E) (hf : ExpertFoldsCond DP E)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    CondTower P DP E := by
  intro X w hw _ hX Z Z' q
  obtain ⟨Y, hY, hYr⟩ := hq X w Z Z' hX q
  have hZv : Valued DP Z := by
    intro n v hv
    obtain ⟨x, hx⟩ := q.source_valued n v hv
    obtain ⟨z, hz, -⟩ := q.left_reflected n v hv x hx
    exact ⟨z, hz⟩
  exact condTower_instance q hY hYr (hT Z Y q.left_codes hY hZv hYr) (hf X w Z Z' hw hX q)
    hworld

/-- **Tower ⟹ the conditional tower** (from def-lattice's `Tower`, T3).
Source: v6 §1.5; vq-wiki-003
Kind: L
Fidelity: exact
Hyps: as `condTower_of_towerValued` with `Tower` -/
theorem condTower_of_tower [IsLogicalInductor P DP] {E : Expert DP} (hT : Tower P DP E)
    (hq : CondQuotesReflected DP E) (hf : ExpertFoldsCond DP E)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    CondTower P DP E :=
  condTower_of_towerValued (towerValued_of_tower hT) hq hf hworld

/-- **The conditional tower contains the tower on valued sources** (T3 converse): `CondTower`
at the constant weight `1` (P-generable as a constant rational code), with `Z := X` (left
product exact, slack `0`) and `Z' := Y`, gives the Tower instance at every e.c. *valued*
`(X, Y)`. Full `Tower` also ranges over unvalued sources (def-lattice audit r2 fidelity 2);
`CondQuote.source_valued` excludes them, so the converse lands in `TowerValued`. The arrows'
consumers (`ThresholdIneq*` via `source_valued`, `Value` via `Menu.Valued`) never touch unvalued
sources, so nothing downstream weakens.
Source: v6 §1.5 ("Setting `w ≡ 1` recovers the bare tower"); mandate T3 converse
Kind: L
Fidelity: weaker: on valued sources only (the corpus's own quantifier; see the docstring)
Hyps: (a) -/
theorem towerValued_of_condTower {E : Expert DP} (hC : CondTower P DP E) :
    TowerValued P DP E := by
  intro X Y hX hY hval hR
  have hgen : PGenerableRat P (fun _ : ℕ => (1 : ℚ)) :=
    PGenerableRat.ofMachineRatCodes (MachineRatCodes.const 1) P
  refine hC X (fun _ => 1) (fun _ => ⟨zero_le_one, le_rfl⟩) hgen hX X Y ?_
  exact
    { left_codes := hX
      right_codes := hY
      slack := fun _ => 0
      slack_tendsto := tendsto_const_nhds
      source_valued := hval
      left_reflected := fun n v _ x hx => ⟨x, hx, by simp⟩
      right_reflected := fun n v hv => by simpa using hR n v hv }

/-- **`TowerValued ⟺ CondTower`**, assembled: the tower on valued sources gives `CondTower`
(under the channel and fold clauses), and `CondTower` gives back the tower on every valued
source — the two predicates are equivalent modulo the disclosed clauses.
Source: v6 §1.5 ("'tower on every LUV' and 'tower with every observable weight' are one
principle"); mandate T3
Kind: L
Fidelity: weaker: over `TowerValued`, not `Tower` (unvalued sources)
Hyps: (c) `CondQuotesReflected`; `ExpertFoldsCond` ((b)/(c)); `hworld` -/
theorem tower_condTower_square [IsLogicalInductor P DP] {E : Expert DP}
    (hq : CondQuotesReflected DP E) (hf : ExpertFoldsCond DP E)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (TowerValued P DP E → CondTower P DP E) ∧ (CondTower P DP E → TowerValued P DP E) :=
  ⟨fun hT => condTower_of_towerValued hT hq hf hworld, towerValued_of_condTower⟩

end

end Cleanroom.Deference.DefLatticeArrows
